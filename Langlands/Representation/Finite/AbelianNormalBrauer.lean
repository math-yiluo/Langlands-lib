import Langlands.Representation.Finite.BrauerTheoryProof
import Langlands.Representation.Finite.DegreeZeroBrauerSupport
import Langlands.Representation.Finite.VirtualCharacterProof
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Brauer induction relative to an abelian normal subgroup

Deligne--Henniart 1981, Proposition 2.2 (ii): for a finite group `G`, an abelian normal
subgroup `A` and a representation `V` without nonzero `A`-fixed vectors, `V` is an
integral combination of representations induced from rank-one characters of subgroups
containing `A` that are nontrivial on `A`.
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped Classical

namespace Langlands.FiniteRep

universe uG

/-- Actual rank-one inductions from subgroups containing `A`, by characters nontrivial on `A`. -/
def abelianNormalBrauerGenerators (G : Type uG) [Group G] [Fintype G] (A : Subgroup G) :
    Set (VirtualRep ℂ G) :=
  {x | ∃ (S : Subgroup G) (hAS : A ≤ S) (χ : S →* ℂˣ),
    (∃ a : A, χ (Subgroup.inclusion hAS a) ≠ 1) ∧
    x = ofClass (induce S (classOf (oneDimensional χ)))}

/-- The integral span of those inductions in the split representation group. -/
def abelianNormalBrauerSpan (G : Type uG) [Group G] [Fintype G] (A : Subgroup G) :
    Submodule ℤ (VirtualRep ℂ G) :=
  Submodule.span ℤ (abelianNormalBrauerGenerators G A)

/-- Deligne--Henniart 2.2 (ii): a representation without nonzero vectors fixed by an
abelian normal subgroup `A` lies in the span of the `A`-nontrivial inductions. -/
def AbelianNormalBrauerStatement (G : Type uG) [Group G] [Fintype G] : Prop :=
  ∀ A : Subgroup G, A.Normal → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    ∀ V : FDRep ℂ G, (∀ v : V, (∀ a ∈ A, V.ρ a v = v) → v = 0) →
      ofClass (classOf V) ∈ abelianNormalBrauerSpan G A

namespace AbelianNormalBrauer

section Orthogonality

variable {B : Type*} [Group B] [Fintype B]

/-- A nontrivial unit-valued character has vanishing sum. -/
theorem sum_char_eq_zero (θ : B →* ℂˣ) (hθ : θ ≠ 1) : ∑ b : B, (θ b : ℂ) = 0 := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, θ b₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hθ (MonoidHom.ext h)
  have hs : (θ b₀ : ℂ) * ∑ b : B, (θ b : ℂ) = ∑ b : B, (θ b : ℂ) := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft b₀) _ _ (fun b => by simp [map_mul])
  have h1 : (θ b₀ : ℂ) ≠ 1 := fun h => hb₀ (Units.ext h)
  have h2 : ((θ b₀ : ℂ) - 1) * ∑ b : B, (θ b : ℂ) = 0 := by
    rw [sub_mul, hs, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) h1
  · exact h

end Orthogonality

section Dual

open scoped IsMulCommutative

variable {A : Type*} [Group A] [IsMulCommutative A]

/-- A unit-valued character as an additive character of `Additive A`. -/
def toAddChar (ε : A →* ℂˣ) : AddChar (Additive A) ℂ where
  toFun a := (ε a.toMul : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp

/-- An additive character of `Additive A` as a unit-valued character of `A`. -/
def ofAddChar (ψ : AddChar (Additive A) ℂ) : A →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun a => ψ (Additive.ofMul a)
      map_one' := by simp
      map_mul' := fun a b => by simp [AddChar.map_add_eq_mul] }

/-- Unit-valued and additive characters of a commutative group agree. -/
def charEquiv : (A →* ℂˣ) ≃ AddChar (Additive A) ℂ where
  toFun := toAddChar
  invFun := ofAddChar
  left_inv ε := by ext a; simp [toAddChar, ofAddChar]
  right_inv ψ := by ext a; simp [toAddChar, ofAddChar]

variable [Fintype A]

/-- The finite character group, transported from additive characters. -/
@[instance_reducible] def charFintype : Fintype (A →* ℂˣ) := Fintype.ofEquiv _ charEquiv.symm

attribute [local instance] charFintype in
/-- Dual orthogonality: the sum of all characters at `a`. -/
theorem sum_char_apply (a : A) :
    ∑ ε : A →* ℂˣ, (ε a : ℂ) = if a = 1 then (Nat.card A : ℂ) else 0 := by
  rw [Fintype.sum_equiv charEquiv (fun ε => (ε a : ℂ)) (fun ψ => ψ (Additive.ofMul a))
    (fun ε => rfl), AddChar.sum_apply_eq_ite]
  simp [Nat.card_eq_fintype_card]

end Dual

attribute [local instance] charFintype

section Projection

variable {G : Type uG} [Group G] [Fintype G] (A : Subgroup G)

/-- The `ε`-isotypic projection for left translation by `A`:
`(proj ε f) g = |A|⁻¹ ∑ₐ ε(a)⁻¹ f(a g)`. -/
def proj (ε : A →* ℂˣ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := (Nat.card A : ℂ)⁻¹ * ∑ a : A, (ε a⁻¹ : ℂ) * f (a * g)
  map_add' f h := by
    ext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem proj_apply (ε : A →* ℂˣ) (f : G → ℂ) (g : G) :
    proj A ε f g = (Nat.card A : ℂ)⁻¹ * ∑ a : A, (ε a⁻¹ : ℂ) * f (a * g) := rfl

theorem card_ne_zero : (Nat.card A : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.card_pos (α := A)).ne'

/-- (a) The projections over all characters of `A` sum to the identity. -/
theorem sum_proj [IsMulCommutative A] (f : G → ℂ) (g : G) :
    ∑ ε : A →* ℂˣ, proj A ε f g = f g := by
  simp only [proj_apply, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_char_apply, inv_eq_one, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, OneMemClass.coe_one, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (card_ne_zero A), one_mul]

variable [A.Normal]

/-- Conjugation of characters of `A`: `(g • ε) a = ε (g⁻¹ a g)`. -/
def conjChar (g : G) (ε : A →* ℂˣ) : A →* ℂˣ :=
  ε.comp (MulAut.conjNormal g⁻¹).toMonoidHom

omit [Fintype G] in
theorem conjChar_apply (g : G) (ε : A →* ℂˣ) (a : A) :
    conjChar A g ε a = ε (MulAut.conjNormal g⁻¹ a) := rfl

/-- The conjugation action of `G` on the characters of `A`. -/
@[instance_reducible] def charAction : MulAction G (A →* ℂˣ) where
  smul := conjChar A
  one_smul ε := by
    refine MonoidHom.ext fun a => ?_
    change ε (MulAut.conjNormal 1⁻¹ a) = ε a
    simp
  mul_smul g h ε := by
    refine MonoidHom.ext fun a => ?_
    change ε (MulAut.conjNormal (g * h)⁻¹ a) = ε (MulAut.conjNormal h⁻¹ (MulAut.conjNormal g⁻¹ a))
    rw [mul_inv_rev, map_mul, MulAut.mul_apply]

attribute [local instance] charAction

omit [Fintype G] in
theorem smul_char_apply (g : G) (ε : A →* ℂˣ) (a : A) :
    (g • ε) a = ε (MulAut.conjNormal g⁻¹ a) := rfl

/-- The class-function projection transforms by conjugation of the character. -/
theorem proj_conj (ε : A →* ℂˣ) (f : G → ℂ) (hf : ∀ x y : G, f (x * y * x⁻¹) = f y)
    (x g : G) : proj A ε f (x⁻¹ * g * x) = proj A (x • ε) f g := by
  simp only [proj_apply]
  congr 1
  rw [← (MulAut.conjNormal x⁻¹).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  · rw [smul_char_apply]
    congr 2
    apply Subtype.ext
    simp [mul_assoc]
  · rw [← hf x⁻¹ (a * g)]
    congr 1
    simp [mul_assoc]

end Projection

section Operators

variable {G : Type uG} [Group G] [Fintype G] (A : Subgroup G) (V : FDRep ℂ G)

/-- The isotypic idempotent `|A|⁻¹ ∑ₐ ε(a)⁻¹ ρ(a)`. -/
def isoOp (ε : A →* ℂˣ) : V →ₗ[ℂ] V :=
  (Nat.card A : ℂ)⁻¹ • ∑ a : A, (ε a⁻¹ : ℂ) • V.ρ a

theorem proj_character (ε : A →* ℂˣ) (g : G) :
    proj A ε V.character g = LinearMap.trace ℂ V (isoOp A V ε * V.ρ g) := by
  rw [proj_apply, isoOp, smul_mul_assoc, Finset.sum_mul, map_smul, map_sum, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]
  rfl

theorem rho_mul_isoOp (ε : A →* ℂˣ) (b : A) :
    V.ρ b * isoOp A V ε = (ε b : ℂ) • isoOp A V ε := by
  have h : V.ρ b * ∑ a : A, (ε a⁻¹ : ℂ) • V.ρ a =
      (ε b : ℂ) • ∑ a : A, (ε a⁻¹ : ℂ) • V.ρ a := by
    rw [Finset.mul_sum, Finset.smul_sum]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.mulLeft b)]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_smul_comm, smul_smul, Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, ← Units.val_mul]
    congr 2
    rw [mul_inv_rev, map_mul, mul_left_comm, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [isoOp, mul_smul_comm, h, smul_comm]

theorem isoOp_mul_isoOp (η ε : A →* ℂˣ) :
    isoOp A V η * isoOp A V ε =
      ((Nat.card A : ℂ)⁻¹ * ∑ a : A, (η a⁻¹ : ℂ) * ε a) • isoOp A V ε := by
  conv_lhs => rw [isoOp]
  rw [smul_mul_assoc, Finset.sum_mul, mul_smul, Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [smul_mul_assoc, rho_mul_isoOp, smul_smul]

theorem isoOp_idem [IsMulCommutative A] (ε : A →* ℂˣ) :
    isoOp A V ε * isoOp A V ε = isoOp A V ε := by
  rw [isoOp_mul_isoOp]
  have h : ∀ a : A, (ε a⁻¹ : ℂ) * ε a = 1 := fun a => by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, inv_mul_cancel₀ (card_ne_zero A), one_smul]

theorem isoOp_mul_isoOp_of_ne [IsMulCommutative A] (η ε : A →* ℂˣ) (h : η ≠ ε) :
    isoOp A V η * isoOp A V ε = 0 := by
  rw [isoOp_mul_isoOp]
  have hθ : η⁻¹ * ε ≠ 1 := fun e => h (inv_mul_eq_one.mp e)
  have hs := sum_char_eq_zero (η⁻¹ * ε) hθ
  have he : ∀ a : A, ((η⁻¹ * ε) a : ℂ) = (η a⁻¹ : ℂ) * ε a := fun a => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_inv]
  simp only [he] at hs
  rw [hs, mul_zero, zero_smul]

variable [A.Normal]

attribute [local instance] charAction

theorem conj_isoOp (ε : A →* ℂˣ) (g : G) :
    V.ρ g⁻¹ * isoOp A V ε * V.ρ g = isoOp A V (g⁻¹ • ε) := by
  rw [isoOp, isoOp, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [← (MulAut.conjNormal g).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, smul_char_apply]
  congr 2
  · congr 2
    apply Subtype.ext
    simp
  · simp [mul_assoc]

theorem isoOp_mul_rho (ε : A →* ℂˣ) (g : G) :
    isoOp A V ε * V.ρ g = V.ρ g * isoOp A V (g⁻¹ • ε) := by
  rw [← conj_isoOp, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

/-- (b) The projected character vanishes off the stabilizer of the character. -/
theorem proj_character_eq_zero [IsMulCommutative A] (ε : A →* ℂˣ) (g : G)
    (hg : g ∉ MulAction.stabilizer G ε) : proj A ε V.character g = 0 := by
  have hne : g⁻¹ • ε ≠ ε := by
    intro h
    apply hg
    rw [MulAction.mem_stabilizer_iff]
    calc g • ε = g • (g⁻¹ • ε) := by rw [h]
      _ = ε := smul_inv_smul g ε
  rw [proj_character]
  calc LinearMap.trace ℂ V (isoOp A V ε * V.ρ g)
      = LinearMap.trace ℂ V (isoOp A V ε * isoOp A V ε * V.ρ g) := by rw [isoOp_idem]
    _ = LinearMap.trace ℂ V (isoOp A V ε * (V.ρ g * isoOp A V (g⁻¹ • ε))) := by
        rw [mul_assoc, isoOp_mul_rho]
    _ = LinearMap.trace ℂ V ((V.ρ g * isoOp A V (g⁻¹ • ε)) * isoOp A V ε) := by
        rw [LinearMap.trace_mul_comm]
    _ = LinearMap.trace ℂ V (V.ρ g * (isoOp A V (g⁻¹ • ε) * isoOp A V ε)) := by
        rw [mul_assoc]
    _ = 0 := by rw [isoOp_mul_isoOp_of_ne A V _ _ hne, mul_zero, map_zero]

omit [A.Normal] in
/-- (c) Without nonzero `A`-fixed vectors the trivial projection vanishes. -/
theorem proj_one_character (hV : ∀ v : V, (∀ a ∈ A, V.ρ a v = v) → v = 0) (g : G) :
    proj A 1 V.character g = 0 := by
  have hz : isoOp A V 1 = 0 := by
    ext v
    apply hV
    intro a ha
    have h := congrArg (fun T : V →ₗ[ℂ] V => T v) (rho_mul_isoOp A V 1 ⟨a, ha⟩)
    simpa using h
  rw [proj_character, hz, zero_mul, map_zero]

end Operators

section Orbits

variable {G : Type uG} [Group G] [Fintype G] (A : Subgroup G) [A.Normal]

attribute [local instance] charAction

theorem card_filter_smul (r ε : A →* ℂˣ) (h : ε ∈ MulAction.orbit G r) :
    (Finset.univ.filter fun x : G => x • r = ε).card =
      Nat.card (MulAction.stabilizer G r) := by
  obtain ⟨y, rfl⟩ := h
  rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  refine Fintype.card_congr
    { toFun := fun x => ⟨y⁻¹ * x.1, ?_⟩
      invFun := fun s => ⟨y * s.1, ?_⟩
      left_inv := fun x => Subtype.ext (mul_inv_cancel_left y x.1)
      right_inv := fun s => Subtype.ext (inv_mul_cancel_left y s.1) }
  · rw [MulAction.mem_stabilizer_iff, mul_smul, x.2, inv_smul_smul]
  · change (y * s.1) • r = y • r
    rw [mul_smul, MulAction.mem_stabilizer_iff.mp s.2]

/-- Orbit counting: summing over the group counts each orbit point `|Stab|` times. -/
theorem sum_smul_eq [IsMulCommutative A] (r : A →* ℂˣ) (P : (A →* ℂˣ) → ℂ) :
    ∑ x : G, P (x • r) = (Nat.card (MulAction.stabilizer G r) : ℂ) *
      ∑ ε : A →* ℂˣ, if ε ∈ MulAction.orbit G r then P ε else 0 := by
  rw [← Finset.sum_fiberwise Finset.univ (fun x : G => x • r), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  split_ifs with h
  · rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, card_filter_smul A r ε h, nsmul_eq_mul]
  · rw [mul_zero]
    apply Finset.sum_eq_zero
    intro x hx
    exact absurd ⟨x, (Finset.mem_filter.mp hx).2⟩ h

end Orbits

section Pairing

open DegreeZeroBrauer

variable {H : Type uG} [Group H] [Fintype H] (A : Subgroup H) (η : A →* ℂˣ)
  (S : Subgroup H) (χ : S →* ℂˣ)

/-- The scalar `∑_{c ∈ A ∩ S} η(c)⁻¹ χ(c)`, written as a sum over `A`. -/
def pairing : ℂ := ∑ c : A, (η c⁻¹ : ℂ) * extend S (fun s => (χ s : ℂ)) c

omit [Fintype H] in
theorem extend_mul_right (y : H) (s : S) :
    extend S (fun s => (χ s : ℂ)) (y * s) = extend S (fun s => (χ s : ℂ)) y * χ s := by
  unfold extend
  by_cases hy : y ∈ S
  · have hys : y * s ∈ S := S.mul_mem hy s.2
    rw [dite_eq_left hys, dite_eq_left hy, ← Units.val_mul, ← map_mul]
    rfl
  · have hys : y * s ∉ S := fun h => hy (by simpa using S.mul_mem h (S.inv_mem s.2))
    rw [dite_eq_right hys, dite_eq_right hy, zero_mul]

omit [Fintype H] in
theorem extend_mul_left (s : S) (y : H) :
    extend S (fun s => (χ s : ℂ)) (s * y) = χ s * extend S (fun s => (χ s : ℂ)) y := by
  unfold extend
  by_cases hy : y ∈ S
  · have hys : (s : H) * y ∈ S := S.mul_mem s.2 hy
    rw [dite_eq_left hys, dite_eq_left hy, ← Units.val_mul, ← map_mul]
    rfl
  · have hys : (s : H) * y ∉ S := fun h => hy (by simpa using S.mul_mem (S.inv_mem s.2) h)
    rw [dite_eq_right hys, dite_eq_right hy, mul_zero]

/-- If `η` and `χ` differ on `A ∩ S`, the pairing vanishes. -/
theorem pairing_eq_zero (h : ∃ (c : A) (hS : (c : H) ∈ S), η c ≠ χ ⟨c, hS⟩) :
    pairing A η S χ = 0 := by
  obtain ⟨c₀, hS, hne⟩ := h
  set k : ℂˣ := (η c₀)⁻¹ * χ ⟨c₀, hS⟩ with hk_def
  have hs : pairing A η S χ = (k : ℂ) * pairing A η S χ := by
    unfold pairing
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft c₀)]
    apply Finset.sum_congr rfl
    intro a _
    have e : (((Equiv.mulLeft c₀) a : A) : H) = ((⟨c₀, hS⟩ : S) : H) * a := rfl
    rw [e, extend_mul_left, Equiv.coe_mulLeft, mul_inv_rev, map_mul, map_inv η c₀, hk_def]
    push_cast
    ring
  have hk : (k : ℂ) ≠ 1 := fun h => hne (inv_mul_eq_one.mp (Units.val_eq_one.mp h))
  have h2 : ((k : ℂ) - 1) * pairing A η S χ = 0 := by
    rw [sub_mul, ← hs, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hk
  · exact h

/-- If `η` and `χ` agree on `A ∩ S`, the pairing is the order of `A ∩ S`. -/
theorem pairing_eq_card (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩) :
    pairing A η S χ = ((Finset.univ.filter fun c : A => (c : H) ∈ S).card : ℂ) := by
  unfold pairing
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  unfold extend
  dsimp only
  split_ifs with hS
  · rw [← hc c hS, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Nat.cast_one]
  · rw [mul_zero, Nat.cast_zero]

/-- Counting: `|A ⊔ S| · |A ∩ S| = |A| · |S|` for normal `A`. -/
theorem card_sup_mul [A.Normal] :
    Nat.card ↥(A ⊔ S) * (Finset.univ.filter fun c : A => (c : H) ∈ S).card =
      Nat.card A * Nat.card S := by
  have h1 : (Finset.univ.filter fun c : A => (c : H) ∈ S).card = Nat.card (A.subgroupOf S) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr
      { toFun := fun c => ⟨⟨c.1.1, c.2⟩, c.1.2⟩
        invFun := fun s => ⟨⟨s.1.1, s.2⟩, s.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h2 := Subgroup.card_mul_index (A.subgroupOf S)
  have h3 := Subgroup.card_mul_index (A.subgroupOf (A ⊔ S))
  have h4 : (A.subgroupOf (A ⊔ S)).index = (A.subgroupOf S).index :=
    Subgroup.relIndex_sup_left S A
  have h5 : Nat.card (A.subgroupOf (A ⊔ S)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  rw [h1, ← h2, ← h3, h4, h5]
  ring

variable [A.Normal]

omit [A.Normal] in
theorem sum_extend_of_mem (a₀ : A) (s₀ : S) :
    ∑ a : A, (η a⁻¹ : ℂ) * extend S (fun s => (χ s : ℂ)) (a * ((a₀ : H) * s₀)) =
      (η a₀ : ℂ) * χ s₀ * pairing A η S χ := by
  unfold pairing
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulRight a₀⁻¹)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.coe_mulRight]
  have e : ((a * a₀⁻¹ : A) : H) * ((a₀ : H) * s₀) = (a : H) * s₀ := by
    simp [mul_assoc]
  rw [e, extend_mul_right, mul_inv_rev, inv_inv, map_mul]
  push_cast
  ring

omit [A.Normal] in
theorem sum_extend_of_not_mem (y : H) (hy : y ∉ A ⊔ S) :
    ∑ a : A, (η a⁻¹ : ℂ) * extend S (fun s => (χ s : ℂ)) (a * y) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  have h : (a : H) * y ∉ S := fun h => hy (by
    simpa using Subgroup.mul_mem_sup (A.inv_mem a.2) h)
  simp [extend, h]

/-- The projection of an induced rank-one character, as a double sum. -/
theorem proj_ind (hη : ∀ (h : H) (a : A), η (MulAut.conjNormal h a) = η a) (g : H) :
    proj A η (ind S (fun s => (χ s : ℂ))) g = (Nat.card A : ℂ)⁻¹ * ((Nat.card S : ℂ)⁻¹ *
      ∑ x : H, ∑ a : A, (η a⁻¹ : ℂ) * extend S (fun s => (χ s : ℂ)) (a * (x⁻¹ * g * x))) := by
  rw [proj_apply]
  congr 1
  simp only [ind_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← (MulAut.conjNormal x).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  have e1 : x⁻¹ * ((MulAut.conjNormal x a : H) * g) * x = (a : H) * (x⁻¹ * g * x) := by
    simp [MulAut.conjNormal_apply, mul_assoc]
  have key : (η (MulAut.conjNormal x a)⁻¹ : ℂ) * ((Nat.card S : ℂ)⁻¹ *
      extend S (fun s => (χ s : ℂ)) (x⁻¹ * ((MulAut.conjNormal x a : H) * g) * x)) =
      (Nat.card S : ℂ)⁻¹ * ((η a⁻¹ : ℂ) *
        extend S (fun s => (χ s : ℂ)) (a * (x⁻¹ * g * x))) := by
    rw [← map_inv (MulAut.conjNormal x) a, hη, e1]
    ring
  exact key

/-- Lemma C, vanishing case. -/
theorem proj_ind_eq_zero (hη : ∀ (h : H) (a : A), η (MulAut.conjNormal h a) = η a)
    (hc : ∃ (c : A) (hS : (c : H) ∈ S), η c ≠ χ ⟨c, hS⟩) :
    proj A η (ind S (fun s => (χ s : ℂ))) = 0 := by
  funext g
  rw [proj_ind A η S χ hη, Pi.zero_apply]
  have h0 : ∀ x : H, ∑ a : A, (η a⁻¹ : ℂ) *
      extend S (fun s => (χ s : ℂ)) (a * (x⁻¹ * g * x)) = 0 := by
    intro x
    by_cases hy : x⁻¹ * g * x ∈ A ⊔ S
    · obtain ⟨a₀, ha₀, s₀, hs₀, he⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      rw [← he]
      exact (sum_extend_of_mem A η S χ ⟨a₀, ha₀⟩ ⟨s₀, hs₀⟩).trans
        (by rw [pairing_eq_zero A η S χ hc, mul_zero])
    · exact sum_extend_of_not_mem A η S χ _ hy
  simp only [h0, Finset.sum_const_zero, mul_zero]

omit [Fintype H] in
theorem exists_decomp (k : ↥(A ⊔ S)) : ∃ a : A, ∃ s : S, (a : H) * s = k := by
  obtain ⟨y, hy, z, hz, h⟩ := Subgroup.mem_sup_of_normal_left.mp k.2
  exact ⟨⟨y, hy⟩, ⟨z, hz⟩, h⟩

omit [Fintype H] [A.Normal] in
theorem pair_eq (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩)
    (a a' : A) (s s' : S) (h : (a : H) * s = a' * s') :
    η a * χ s = η a' * χ s' := by
  have hcs : ((a'⁻¹ * a : A) : H) = ((s' * s⁻¹ : S) : H) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have hS : ((a'⁻¹ * a : A) : H) ∈ S := by
    rw [hcs]
    exact (s' * s⁻¹).2
  have key := hc _ hS
  rw [show (⟨((a'⁻¹ * a : A) : H), hS⟩ : S) = s' * s⁻¹ from Subtype.ext hcs, map_mul,
    map_mul, map_inv, map_inv] at key
  calc η a * χ s = η a' * ((η a')⁻¹ * η a) * χ s := by group
    _ = η a' * (χ s' * (χ s)⁻¹) * χ s := by rw [key]
    _ = η a' * χ s' := by group

/-- The values of the product character, via a chosen decomposition. -/
def supFun (k : ↥(A ⊔ S)) : ℂˣ :=
  η (exists_decomp A S k).choose * χ (exists_decomp A S k).choose_spec.choose

omit [Fintype H] in
theorem supFun_eq (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩)
    (k : ↥(A ⊔ S)) (a : A) (s : S) (h : (a : H) * s = k) : supFun A η S χ k = η a * χ s := by
  unfold supFun
  exact pair_eq A η S χ hc _ _ _ _
    ((exists_decomp A S k).choose_spec.choose_spec.trans h.symm)

/-- The character `a s ↦ η(a) χ(s)` of `A ⊔ S`. -/
def supChar (hη : ∀ (h : H) (a : A), η (MulAut.conjNormal h a) = η a)
    (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩) : ↥(A ⊔ S) →* ℂˣ where
  toFun := supFun A η S χ
  map_one' := by
    rw [supFun_eq A η S χ hc 1 1 1 (by simp), map_one, map_one, mul_one]
  map_mul' k k' := by
    obtain ⟨a, s, h⟩ := exists_decomp A S k
    obtain ⟨a', s', h'⟩ := exists_decomp A S k'
    rw [supFun_eq A η S χ hc k a s h, supFun_eq A η S χ hc k' a' s' h',
      supFun_eq A η S χ hc (k * k') (a * MulAut.conjNormal (s : H) a') (s * s') ?_,
      map_mul, map_mul, hη]
    · exact mul_mul_mul_comm _ _ _ _
    · simp [MulAut.conjNormal_apply, ← h, ← h', mul_assoc]

omit [Fintype H] in
theorem supChar_apply_of_mem (hη : ∀ (h : H) (a : A), η (MulAut.conjNormal h a) = η a)
    (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩) (k : ↥(A ⊔ S)) (a : A)
    (hk : (k : H) = a) : supChar A η S χ hη hc k = η a := by
  change supFun A η S χ k = η a
  rw [supFun_eq A η S χ hc k a 1 (by simp [hk]), map_one, mul_one]

/-- Lemma C, nonvanishing case: the projection is induced from `A ⊔ S`. -/
theorem proj_ind_eq (hη : ∀ (h : H) (a : A), η (MulAut.conjNormal h a) = η a)
    (hc : ∀ (c : A) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩) :
    proj A η (ind S (fun s => (χ s : ℂ))) =
      ind (A ⊔ S) (fun k => (supChar A η S χ hη hc k : ℂ)) := by
  funext g
  have hind : ind (A ⊔ S) (fun k => (supChar A η S χ hη hc k : ℂ)) g =
      (Nat.card ↥(A ⊔ S) : ℂ)⁻¹ * ∑ x : H,
        extend (A ⊔ S) (fun k => (supChar A η S χ hη hc k : ℂ)) (x⁻¹ * g * x) :=
    ind_apply _ _ _
  rw [proj_ind A η S χ hη, hind]
  have hΦ : ∀ y : H, ∑ a : A, (η a⁻¹ : ℂ) * extend S (fun s => (χ s : ℂ)) (a * y) =
      pairing A η S χ * extend (A ⊔ S) (fun k => (supChar A η S χ hη hc k : ℂ)) y := by
    intro y
    by_cases hy : y ∈ A ⊔ S
    · obtain ⟨a₀, ha₀, s₀, hs₀, he⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      have hext : extend (A ⊔ S) (fun k => (supChar A η S χ hη hc k : ℂ)) y =
          (supFun A η S χ ⟨y, hy⟩ : ℂ) := dite_eq_left hy
      rw [hext, supFun_eq A η S χ hc ⟨y, hy⟩ ⟨a₀, ha₀⟩ ⟨s₀, hs₀⟩ he]
      subst he
      exact (sum_extend_of_mem A η S χ ⟨a₀, ha₀⟩ ⟨s₀, hs₀⟩).trans (by push_cast; ring)
    · rw [sum_extend_of_not_mem A η S χ y hy]
      simp [extend, hy]
  simp only [hΦ, ← Finset.mul_sum]
  rw [pairing_eq_card A η S χ hc]
  have hcard : (Nat.card ↥(A ⊔ S) : ℂ) *
      ((Finset.univ.filter fun c : A => (c : H) ∈ S).card : ℂ) =
      (Nat.card A : ℂ) * Nat.card S := by
    exact_mod_cast card_sup_mul A S
  have hK := card_ne_zero (A ⊔ S)
  have hA := card_ne_zero A
  have hS := card_ne_zero S
  have ht : ((Finset.univ.filter fun c : A => (c : H) ∈ S).card : ℂ) =
      (Nat.card A : ℂ) * Nat.card S / Nat.card ↥(A ⊔ S) := by
    rw [eq_div_iff hK, mul_comm, hcard]
  rw [ht]
  field_simp

end Pairing

section Assembly

open DegreeZeroBrauer

variable {G : Type uG} [Group G] [Fintype G] (A : Subgroup G)

/-- The character image of the span of `A`-nontrivial inductions. -/
def charSpan : Submodule ℤ (G → ℂ) :=
  (abelianNormalBrauerSpan G A).map (virtualCharacter (k := ℂ) (G := G))

theorem ind_generator_mem (K : Subgroup G) (hAK : A ≤ K) (μ : K →* ℂˣ)
    (hμ : ∃ a : A, μ (Subgroup.inclusion hAK a) ≠ 1) :
    ind K (fun k => (μ k : ℂ)) ∈ charSpan A := by
  refine ⟨ofClass (induce K (classOf (oneDimensional μ))),
    Submodule.subset_span ⟨K, hAK, μ, hμ, rfl⟩, ?_⟩
  rw [virtualCharacter_ofClass]
  change (induceRep K (oneDimensional μ)).character = _
  rw [← ind_character]
  congr 1
  funext k
  exact character_oneDimensional μ k

variable [A.Normal]

/-- Induction to `G` of the `η`-projection of a virtual character of `H ⊇ A`. -/
theorem ind_proj_mem (H : Subgroup G) (hAH : A ≤ H) (η : A.subgroupOf H →* ℂˣ)
    (hη : ∀ (h : H) (a : A.subgroupOf H), η (MulAut.conjNormal h a) = η a) (hne : η ≠ 1)
    {f : H → ℂ} (hf : f ∈ inducedCharacterLattice (k := ℂ) (G := H)) :
    ind H (proj (A.subgroupOf H) η f) ∈ charSpan A := by
  have : (A.subgroupOf H).Normal := Subgroup.Normal.subgroupOf ‹_› H
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨S, χ⟩, rfl⟩ := hy
    have hy : inducedCharacter (k := ℂ) (⟨S, χ⟩ : MonomialDatum ℂ H) =
        ind S (fun s => (χ s : ℂ)) := by
      change (induceRep S (oneDimensional χ)).character = _
      rw [← ind_character]
      congr 1
      funext s
      exact character_oneDimensional χ s
    rw [hy]
    by_cases hc : ∀ (c : A.subgroupOf H) (hS : (c : H) ∈ S), η c = χ ⟨c, hS⟩
    · rw [proj_ind_eq _ η S χ hη hc, ind_ind]
      have hAK : A ≤ (A.subgroupOf H ⊔ S).map H.subtype := by
        intro a ha
        exact ⟨⟨a, hAH ha⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
      let e := (A.subgroupOf H ⊔ S).equivMapOfInjective H.subtype H.subtype_injective
      obtain ⟨a', ha'⟩ : ∃ a', η a' ≠ 1 := by
        by_contra h
        push Not at h
        exact hne (MonoidHom.ext h)
      refine ind_generator_mem A _ hAK ((supChar _ η S χ hη hc).comp e.symm.toMonoidHom)
        ⟨⟨(a' : H), a'.2⟩, ?_⟩
      rw [MonoidHom.comp_apply, supChar_apply_of_mem _ η S χ hη hc _ a' ?_]
      · exact ha'
      · apply Subtype.ext
        have h2 := congrArg Subtype.val
          (e.apply_symm_apply (Subgroup.inclusion hAK ⟨(a' : H), a'.2⟩))
        exact h2
    · push Not at hc
      rw [proj_ind_eq_zero _ η S χ hη hc, map_zero]
      exact Submodule.zero_mem _
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  | smul n x _ hx => rw [map_zsmul, map_zsmul]; exact Submodule.smul_mem _ n hx

omit [A.Normal] in
/-- The projection commutes with restriction to a subgroup containing `A`. -/
theorem proj_subgroupOf (H : Subgroup G) (hAH : A ≤ H) (r : A →* ℂˣ) (φ : G → ℂ) (h : H) :
    proj (A.subgroupOf H) (r.comp (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom)
      (fun h => φ h) h = proj A r φ h := by
  rw [proj_apply, proj_apply, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]
  congr 1
  exact Fintype.sum_equiv (Subgroup.subgroupOfEquivOfLe hAH).toEquiv _ _ (fun a => rfl)

attribute [local instance] charAction

omit [Fintype G] in
theorem le_stabilizer [IsMulCommutative A] (r : A →* ℂˣ) : A ≤ MulAction.stabilizer G r := by
  intro a ha
  rw [MulAction.mem_stabilizer_iff]
  refine MonoidHom.ext fun b => ?_
  rw [smul_char_apply]
  congr 1
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, inv_inv,
    setLike_mul_comm (A.inv_mem ha) b.2, inv_mul_cancel_right]

/-- A nontrivial projection, restricted to a subgroup fixing it, induces into the span. -/
theorem ind_proj_restrict_mem (V : FDRep ℂ G) (r : A →* ℂˣ) (hr : r ≠ 1) (H : Subgroup G)
    (hAH : A ≤ H) (hH : ∀ h ∈ H, h • r = r) :
    ind H (fun h => proj A r V.character h) ∈ charSpan A := by
  have hres : (fun h : H => proj A r V.character h) =
      proj (A.subgroupOf H) (r.comp (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom)
        (fun h : H => V.character h) :=
    funext fun h => (proj_subgroupOf A H hAH r V.character h).symm
  rw [hres]
  apply ind_proj_mem A H hAH
  · intro h a
    have hh : ((h : G)⁻¹) • r = r := hH _ (H.inv_mem h.2)
    change r _ = r _
    conv_rhs => rw [← hh]
    rw [smul_char_apply]
    congr 1
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
  · intro h1
    apply hr
    refine MonoidHom.ext fun a => ?_
    have := congrArg (fun φ : A.subgroupOf H →* ℂˣ => φ ((Subgroup.subgroupOfEquivOfLe hAH).symm a)) h1
    simpa using this
  · rw [BrauerLattice.characterLattice]
    exact ⟨ofClass (classOf (FDRep.of (V.ρ.comp H.subtype))), by
      rw [virtualCharacter_ofClass, character_classOf]; rfl⟩

/-- (d) Induction from the stabilizer collects the projections over an orbit. -/
theorem ind_proj_stabilizer [IsMulCommutative A] (V : FDRep ℂ G) (r : A →* ℂˣ) (g : G) :
    ind (MulAction.stabilizer G r) (fun h => proj A r V.character h) g =
      ∑ ε : A →* ℂˣ, if ε ∈ MulAction.orbit G r then proj A ε V.character g else 0 := by
  have hf : ∀ x y : G, V.character (x * y * x⁻¹) = V.character y := fun x y => V.char_conj y x
  rw [ind_apply]
  trans (Nat.card (MulAction.stabilizer G r) : ℂ)⁻¹ * ∑ x : G, proj A (x • r) V.character g
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with hx
    · exact proj_conj A r _ hf x g
    · rw [← proj_conj A r _ hf x g, proj_character_eq_zero A V r _ hx]
  rw [sum_smul_eq A r (fun ε => proj A ε V.character g), ← mul_assoc,
    inv_mul_cancel₀ (card_ne_zero _), one_mul]

/-- (e) The character is the sum over orbits of the inductions from the stabilizers. -/
theorem character_eq_sum_orbits [IsMulCommutative A] (V : FDRep ℂ G) (g : G) :
    V.character g = ∑ q : MulAction.orbitRel.Quotient G (A →* ℂˣ),
      ind (MulAction.stabilizer G q.out) (fun h => proj A q.out V.character h) g := by
  simp only [ind_proj_stabilizer]
  rw [Finset.sum_comm, ← sum_proj A V.character g]
  apply Finset.sum_congr rfl
  intro ε _
  rw [Finset.sum_eq_single (Quotient.mk'' ε : MulAction.orbitRel.Quotient G (A →* ℂˣ))]
  · rw [ite_eq_left]
    have := MulAction.orbitRel.Quotient.mem_orbit.mpr
      (rfl : (Quotient.mk'' ε : MulAction.orbitRel.Quotient G (A →* ℂˣ)) = Quotient.mk'' ε)
    rwa [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'] at this
  · intro q _ hq
    rw [ite_eq_right]
    intro hε
    rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq'] at hε
    exact hq (MulAction.orbitRel.Quotient.mem_orbit.mp hε).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ind_stabilizer_mem [IsMulCommutative A] (V : FDRep ℂ G)
    (hV : ∀ v : V, (∀ a ∈ A, V.ρ a v = v) → v = 0) (r : A →* ℂˣ) :
    ind (MulAction.stabilizer G r) (fun h => proj A r V.character h) ∈ charSpan A := by
  by_cases hr : r = 1
  · subst hr
    have h0 : (fun h : MulAction.stabilizer G (1 : A →* ℂˣ) => proj A 1 V.character h) = 0 :=
      funext fun h => proj_one_character A V hV h
    rw [h0, map_zero]
    exact Submodule.zero_mem _
  exact ind_proj_restrict_mem A V r hr _ (le_stabilizer A r)
    (fun h hh => MulAction.mem_stabilizer_iff.mp hh)

end Assembly

end AbelianNormalBrauer

open AbelianNormalBrauer DegreeZeroBrauer in
/-- Deligne--Henniart 1981, Proposition 2.2 (ii). -/
theorem abelianNormalBrauer (G : Type uG) [Group G] [Fintype G] :
    AbelianNormalBrauerStatement G := by
  intro A hAn hA V hV
  have : A.Normal := hAn
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hA a a.2 b b.2)⟩⟩
  let : Fintype (A →* ℂˣ) := charFintype
  let := charAction A
  have hmem : V.character ∈ charSpan A := by
    have he : V.character = ∑ q : MulAction.orbitRel.Quotient G (A →* ℂˣ),
        ind (MulAction.stabilizer G q.out) (fun h => proj A q.out V.character h) := by
      funext g
      rw [Finset.sum_apply]
      exact character_eq_sum_orbits A V g
    rw [he]
    apply Submodule.sum_mem
    intro q _
    exact ind_stabilizer_mem A V hV q.out
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyV : y = ofClass (classOf V) := VirtualCharacter.faithfulness
    (hyx.trans (by rw [virtualCharacter_ofClass, character_classOf]))
  exact hyV ▸ hy

end Langlands.FiniteRep
