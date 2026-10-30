import Langlands.Analysis.Local.QuotientTopology

/-!
# Left quotients for a split group retraction

If `r ∘ s = id` and `H` contains the section, inclusion of `ker r` induces
a homeomorphism `(H ∩ ker r) \ ker r ≃ₜ H \ G`.
-/

namespace Langlands.QuotientIntegration

universe uG uL

variable {G : Type uG} {L : Type uL} [Group G] [Group L]

/-- The actual kernel coordinate of a split group retraction. -/
def splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (g : G) : r.ker :=
  ⟨(s (r g))⁻¹ * g, by
    change r ((s (r g))⁻¹ * g) = 1
    rw [map_mul, map_inv, hrs, inv_mul_cancel]⟩

@[simp] theorem coe_splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (g : G) :
    (splitKernelCoordinate r s hrs g : G) = (s (r g))⁻¹ * g := rfl

/-- The kernel coordinate is sent to `1` by the retraction. -/
theorem map_splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (g : G) :
    r (splitKernelCoordinate r s hrs g : G) = 1 :=
  MonoidHom.mem_ker.mp (splitKernelCoordinate r s hrs g).property

@[simp] theorem splitKernelCoordinate_coe (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (g : r.ker) :
    splitKernelCoordinate r s hrs (g : G) = g := by
  apply Subtype.ext
  have hg : r (g : G) = 1 := g.property
  simp only [coe_splitKernelCoordinate, hg, map_one, inv_one, one_mul]

/-- Multiplying the section coordinate and kernel coordinate recovers the group element. -/
theorem section_mul_splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (g : G) :
    s (r g) * (splitKernelCoordinate r s hrs g : G) = g :=
  mul_inv_cancel_left _ _

/-- Inclusion of the actual kernel descends to the actual left-coset quotient. -/
def kernelLeftQuotientInclusion (r : G →* L) (H : Subgroup G) :
    Langlands.Induction.LeftQuotient (H.comap r.ker.subtype) →
      Langlands.Induction.LeftQuotient H :=
  Quotient.map' (fun x : r.ker => (x : G)) (by
    intro x y h
    rw [QuotientGroup.rightRel_apply] at h ⊢
    exact h)

@[simp] theorem kernelLeftQuotientInclusion_mk (r : G →* L) (H : Subgroup G)
    (g : r.ker) :
    kernelLeftQuotientInclusion r H (leftQuotientMap (H.comap r.ker.subtype) g) =
      leftQuotientMap H (g : G) := rfl

/-- Taking the kernel coordinate respects the coset relation when the section lies in `H`. -/
theorem splitKernelCoordinate_rel (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    {x y : G} (hxy : QuotientGroup.rightRel H x y) :
    QuotientGroup.rightRel (H.comap r.ker.subtype)
      (splitKernelCoordinate r s hrs x) (splitKernelCoordinate r s hrs y) := by
  rw [QuotientGroup.rightRel_apply] at hxy ⊢
  change ((s (r y))⁻¹ * y) * ((s (r x))⁻¹ * x)⁻¹ ∈ H
  have h := H.mul_mem (H.mul_mem (H.inv_mem (hsH (r y))) hxy) (hsH (r x))
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using h

/-- An element and its kernel coordinate lie in the same left coset `H g`. -/
theorem leftQuotientMap_splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hsH : ∀ l, s l ∈ H) (g : G) :
    leftQuotientMap H (splitKernelCoordinate r s hrs g : G) = leftQuotientMap H g := by
  rw [leftQuotientMap_apply, leftQuotientMap_apply]
  apply Quotient.sound
  change QuotientGroup.rightRel H (splitKernelCoordinate r s hrs g : G) g
  rw [QuotientGroup.rightRel_apply]
  change g * ((s (r g))⁻¹ * g)⁻¹ ∈ H
  simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_left] using hsH (r g)

variable [TopologicalSpace G] [TopologicalSpace L] [IsTopologicalGroup G]

/-- The kernel coordinate is continuous for continuous retraction and section. -/
theorem continuous_splitKernelCoordinate (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s) :
    Continuous (splitKernelCoordinate r s hrs) :=
  ((hs.comp hr).inv.mul continuous_id).subtype_mk _

/-- Inclusion of the kernel identifies its intersection quotient with the
ambient left quotient. Both spaces carry their actual quotient topologies. -/
def splitKernelLeftQuotientHomeomorph (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (hr : Continuous r) (hs : Continuous s)
    (H : Subgroup G) (hsH : ∀ l, s l ∈ H) :
    Langlands.Induction.LeftQuotient (H.comap r.ker.subtype) ≃ₜ
      Langlands.Induction.LeftQuotient H where
  toFun := kernelLeftQuotientInclusion r H
  invFun := Quotient.map' (splitKernelCoordinate r s hrs)
    (fun _ _ h => splitKernelCoordinate_rel r s hrs H hsH h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h g =>
      change Quotient.mk _ (splitKernelCoordinate r s hrs (g : G)) = Quotient.mk _ g
      rw [splitKernelCoordinate_coe]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h g => exact leftQuotientMap_splitKernelCoordinate r s hrs H hsH g
  continuous_toFun := continuous_subtype_val.quotient_map' _
  continuous_invFun := (continuous_splitKernelCoordinate r s hrs hr hs).quotient_map' _

@[simp] theorem splitKernelLeftQuotientHomeomorph_mk
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (g : r.ker) :
    splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH
      (leftQuotientMap (H.comap r.ker.subtype) g) =
        leftQuotientMap H (g : G) := rfl

@[simp] theorem splitKernelLeftQuotientHomeomorph_symm_mk
    (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (hr : Continuous r) (hs : Continuous s) (H : Subgroup G) (hsH : ∀ l, s l ∈ H)
    (g : G) :
    (splitKernelLeftQuotientHomeomorph r s hrs hr hs H hsH).symm
      (leftQuotientMap H g) =
        leftQuotientMap (H.comap r.ker.subtype) (splitKernelCoordinate r s hrs g) := rfl

end Langlands.QuotientIntegration
