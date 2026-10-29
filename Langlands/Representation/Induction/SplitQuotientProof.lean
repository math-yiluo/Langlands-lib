import Langlands.Representation.Induction.SplitQuotientStatement

/-!
# Compact induction across a continuous split quotient: proof

For a continuous retraction `r : G →* L` with continuous section `s` and a subgroup
`H ⊇ ker r`, restriction `f ↦ f ∘ s` identifies compact induction from `H`, restricted along
`s`, with compact induction from `H.comap s`; on kernel-trivial coefficients its inverse is
`k ↦ k ∘ r`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Induction

universe uR uG uL uV

section SplitQuotient

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]
variable {G : Type uG} [Group G] {L : Type uL} [Group L]

/-- The element `g * s (r g)⁻¹` lies in the kernel of the retraction `r`. -/
theorem splitQuotient_mul_inv_mem_ker (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (g : G) : g * (s (r g))⁻¹ ∈ r.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]

/-- If `ker r ≤ H`, then `s (r g) ∈ H` for every `g ∈ H`. -/
theorem splitQuotient_section_mem (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) {g : G} (hg : g ∈ H) : s (r g) ∈ H := by
  have hm : g * (s (r g))⁻¹ ∈ H := hker (splitQuotient_mul_inv_mem_ker r s hrs g)
  have h := H.mul_mem (H.inv_mem hm) hg
  rwa [mul_inv_rev, inv_inv, inv_mul_cancel_right] at h

/-- The retraction of an element of `H`, as an element of `H.comap s`. -/
def splitQuotientRetract (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (h : H) : H.comap s :=
  ⟨r h, splitQuotient_section_mem r s hrs H hker h.property⟩

/-- On coefficients where `H ∩ ker r` acts trivially, `h` and `s (r h)` act in the same way. -/
theorem splitQuotient_action_retract (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v) (h : H) (v : V) :
    σ (s.subgroupComap H (splitQuotientRetract r s hrs H hker h)) v = σ h v := by
  let p : H := s.subgroupComap H (splitQuotientRetract r s hrs H hker h)
  have hk : r ((p⁻¹ * h : H) : G) = 1 := by
    change r ((s (r (h : G)))⁻¹ * h) = 1
    rw [map_mul, map_inv, hrs, inv_mul_cancel]
  calc σ p v = σ p (σ (p⁻¹ * h) v) := by rw [hσ _ hk v]
    _ = σ (p * (p⁻¹ * h)) v := by rw [map_mul σ p (p⁻¹ * h), Module.End.mul_apply]
    _ = σ h v := by rw [mul_inv_cancel_left]

/-- A covariant function at `g` is its value at `s (r g)`, moved by the kernel element
`g * s (r g)⁻¹`. -/
theorem splitQuotient_apply_eq (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V) (f : G → V)
    (hf : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x)) (g : G) :
    f g = σ ⟨g * (s (r g))⁻¹, hker (splitQuotient_mul_inv_mem_ker r s hrs g)⟩ (f (s (r g))) := by
  have h : f (g * (s (r g))⁻¹ * s (r g)) =
      σ ⟨g * (s (r g))⁻¹, hker (splitQuotient_mul_inv_mem_ker r s hrs g)⟩ (f (s (r g))) :=
    hf ⟨g * (s (r g))⁻¹, hker (splitQuotient_mul_inv_mem_ker r s hrs g)⟩ (s (r g))
  rwa [inv_mul_cancel_right] at h

/-- On kernel-trivial coefficients a covariant function is constant along `g ↦ s (r g)`. -/
theorem splitQuotient_apply_section (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v) (f : G → V)
    (hf : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x)) (g : G) :
    f (s (r g)) = f g := by
  rw [splitQuotient_apply_eq r s hrs H hker σ f hf g,
    hσ _ (MonoidHom.mem_ker.mp (splitQuotient_mul_inv_mem_ker r s hrs g))]

/-- The map `H \ G → (H.comap s) \ L` induced by the retraction `r`. -/
def splitQuotientRetractMap (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) : LeftQuotient H → LeftQuotient (H.comap s) :=
  Quotient.map' r (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    rw [← map_inv r, ← map_mul r]
    exact splitQuotient_section_mem r s hrs H hker hxy)

/-- The map `(H.comap s) \ L → H \ G` induced by the section `s`. -/
def splitQuotientSectionMap (s : L →* G) (H : Subgroup G) :
    LeftQuotient (H.comap s) → LeftQuotient H :=
  Quotient.map' s (by
    intro x y hxy
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    rw [← map_inv s, ← map_mul s]
    exact hxy)

/-- The projected support of `f ∘ s` is the image of the projected support of `f`. -/
theorem quotientSupport_comp_section (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V) (f : G → V)
    (hf : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x)) :
    quotientSupport (H.comap s) (fun l => f (s l)) =
      splitQuotientRetractMap r s hrs H hker '' quotientSupport H f := by
  ext q
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨quotientMap H (s l), ⟨s l, hl, rfl⟩, ?_⟩
    change quotientMap (H.comap s) (r (s l)) = quotientMap (H.comap s) l
    rw [hrs]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨r g, ?_, rfl⟩
    have hg' : f g ≠ 0 := hg
    intro h0
    change f (s (r g)) = 0 at h0
    apply hg'
    rw [splitQuotient_apply_eq r s hrs H hker σ f hf g, h0, map_zero]

/-- The projected support of `k ∘ r` is the image of the projected support of `k`. -/
theorem quotientSupport_comp_retract (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
    (H : Subgroup G) (hker : r.ker ≤ H) (k : L → V) :
    quotientSupport H (fun g => k (r g)) =
      splitQuotientSectionMap s H '' quotientSupport (H.comap s) k := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨quotientMap (H.comap s) (r g), ⟨r g, hg, rfl⟩, ?_⟩
    change quotientMap H (s (r g)) = quotientMap H g
    exact Quotient.sound
      (QuotientGroup.rightRel_apply.mpr (hker (splitQuotient_mul_inv_mem_ker r s hrs g)))
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨s l, ?_, rfl⟩
    have hl' : k l ≠ 0 := hl
    change k (r (s l)) ≠ 0
    rw [hrs]
    exact hl'

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace L] [IsTopologicalGroup L]

omit [IsTopologicalGroup G] [IsTopologicalGroup L] in
/-- The coset map induced by a continuous retraction is continuous. -/
theorem continuous_splitQuotientRetractMap (r : G →* L) (s : L →* G)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hker : r.ker ≤ H) (hr : Continuous r) :
    Continuous (splitQuotientRetractMap r s hrs H hker) :=
  hr.quotient_map' _

omit [IsTopologicalGroup G] [IsTopologicalGroup L] in
/-- The coset map induced by a continuous section is continuous. -/
theorem continuous_splitQuotientSectionMap (s : L →* G) (H : Subgroup G)
    (hs : Continuous s) : Continuous (splitQuotientSectionMap s H) :=
  hs.quotient_map' _

/-- Restriction `f ↦ f ∘ s` of an actual compact induced function. -/
def splitQuotientRestrict (r : G →* L) (hr : Continuous r) (s : L →* G) (hs : Continuous s)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (f : CompactFunctions H σ) : CompactFunctions (H.comap s) (σ.comp (s.subgroupComap H)) :=
  compactFunctionOf (H.comap s) (σ.comp (s.subgroupComap H)) (fun l => eval H σ f.1 (s l))
    (fun p l => by
      change f.1.1.1 (s ((p : L) * l)) = σ (s.subgroupComap H p) (f.1.1.1 (s l))
      rw [map_mul s]
      exact f.1.1.property (s.subgroupComap H p) (s l))
    ((Classical.choose f.1.property).comap s hs)
    (fun y l => by
      have hy := congrArg (fun F : EquivariantFunctions H σ => F.1 (s l))
        (Classical.choose_spec f.1.property ⟨s y, y.property⟩)
      change f.1.1.1 (s (l * y)) = f.1.1.1 (s l)
      rw [map_mul s]
      exact hy)
    (by
      change IsCompact (quotientSupport (H.comap s) (fun l => f.1.1.1 (s l)))
      rw [quotientSupport_comp_section r s hrs H hker σ f.1.1.1 f.1.1.property]
      have hc : IsCompact (quotientSupport H f.1.1.1) := f.2
      exact hc.image (continuous_splitQuotientRetractMap r s hrs H hker hr))

/-- Extension `k ↦ k ∘ r` of an actual compact induced function, for kernel-trivial
coefficients. -/
def splitQuotientExtend (r : G →* L) (hr : Continuous r) (s : L →* G) (hs : Continuous s)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v)
    (k : CompactFunctions (H.comap s) (σ.comp (s.subgroupComap H))) : CompactFunctions H σ :=
  compactFunctionOf H σ (fun g => eval (H.comap s) (σ.comp (s.subgroupComap H)) k.1 (r g))
    (fun h x => by
      change k.1.1.1 (r ((h : G) * x)) = σ h (k.1.1.1 (r x))
      rw [map_mul r, ← splitQuotient_action_retract r s hrs H hker σ hσ h]
      exact k.1.1.property (splitQuotientRetract r s hrs H hker h) (r x))
    ((Classical.choose k.1.property).comap r hr)
    (fun y x => by
      have hy := congrArg
        (fun F : EquivariantFunctions (H.comap s) (σ.comp (s.subgroupComap H)) => F.1 (r x))
        (Classical.choose_spec k.1.property ⟨r y, y.property⟩)
      change k.1.1.1 (r (x * y)) = k.1.1.1 (r x)
      rw [map_mul r]
      exact hy)
    (by
      change IsCompact (quotientSupport H (fun g => k.1.1.1 (r g)))
      rw [quotientSupport_comp_retract r s hrs H hker]
      have hc : IsCompact (quotientSupport (H.comap s) k.1.1.1) := k.2
      exact hc.image (continuous_splitQuotientSectionMap s H hs))

/-- The actual `L`-equivalence `f ↦ f ∘ s`, with inverse `k ↦ k ∘ r`. -/
def splitQuotientEquiv (r : G →* L) (hr : Continuous r) (s : L →* G) (hs : Continuous s)
    (hrs : ∀ l, r (s l) = l) (H : Subgroup G) (hker : r.ker ≤ H) (σ : Representation R H V)
    (hσ : ∀ h : H, r (h : G) = 1 → ∀ v : V, σ h v = v) :
    Representation.Equiv ((compactInduced H σ).comp s)
      (compactInduced (H.comap s) (σ.comp (s.subgroupComap H))) where
  toLinearMap :=
    { toFun := splitQuotientRestrict r hr s hs hrs H hker σ
      map_add' f g := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext l
        rfl
      map_smul' c f := by
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        funext l
        rfl }
  invFun := splitQuotientExtend r hr s hs hrs H hker σ hσ
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact splitQuotient_apply_section r s hrs H hker σ hσ f.1.1.1 f.1.1.property g
  right_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext l
    change k.1.1.1 (r (s l)) = k.1.1.1 l
    rw [hrs]
  isIntertwining' l := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change f.1.1.1 (s x * s l) = f.1.1.1 (s (x * l))
    rw [map_mul s]

end SplitQuotient

/-- Restriction of compact induction along a continuous section of a continuous split quotient
is compact induction from the pulled-back subgroup, naturally in kernel-trivial coefficients. -/
theorem compactInductionSplitQuotient : CompactInductionSplitQuotient.{uG, uV} := by
  intro G L _ _ _ _ _ _ r s hr hs hrs H _hH hker
  refine ⟨fun A hA => splitQuotientEquiv r hr s hs hrs H hker A.representation hA,
    fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_⟩
  intro A B hA hB T f
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  rfl

end Langlands.Induction
