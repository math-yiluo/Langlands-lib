import Langlands.GroupScheme.Rational.LanglandsDecompositionCones
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # The coroot formula for the actual relative Weyl action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (D : RelativeRootReflectionData i)

/-- Evaluation on a supplied coroot, on the full real character space. -/
def realCorootFunctional (α : relativeRoots i) : Module.Dual ℝ (Vstar T) :=
  (pair T).flip ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)

@[simp] theorem realCorootFunctional_apply (α : relativeRoots i) (x : Vstar T) :
    realCorootFunctional i D α x = pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) := rfl

/-- The integral reflection formula extends to the full real character space. -/
theorem RelativeRootReflectionData.real_reflection (α : relativeRoots i) (x : Vstar T) :
    relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α)) x =
      x - pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) • ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    rw [relativeWeylFullRealAction_tmul, relativeWeylLatticeAction_mk, D.action,
      TensorProduct.tmul_sub, pair_tmul_tmul]
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul,
      ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
    congr 1
    congr 1
    simp [mul_comm]
  | add x y hx hy =>
    simp only [map_add, hx, hy, LinearMap.add_apply, add_smul]
    abel

/-- A reflection negates its own root in the real character space. -/
theorem RelativeRootReflectionData.real_reflection_self (α : relativeRoots i) :
    relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α))
      ((1 : ℝ) ⊗ₜ[ℤ] α.val) = -((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  rw [D.real_reflection i, pair_tmul_tmul, D.pair_self]
  norm_num
  module

include D in
/-- The supplied coroot prevents an actual root from vanishing after real extension. -/
theorem RelativeRootReflectionData.one_tmul_ne_zero (α : relativeRoots i) :
    ((1 : ℝ) ⊗ₜ[ℤ] α.val) ≠ (0 : Vstar T) := by
  intro h
  have hp := pair_tmul_tmul (T := T) (1 : ℝ) 1 α.val (D.coroot α)
  rw [h, map_zero, LinearMap.zero_apply, D.pair_self] at hp
  norm_num at hp

/-- Weyl invariance gives the coroot formula without dividing by a root length. -/
theorem RelativeRootReflectionData.coroot_mul_form
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : Vstar T) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) *
        B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) =
      2 * B x ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h := hB.2.2 (QuotientGroup.mk (D.representative α)) x
    ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  rw [D.real_reflection_self i, D.real_reflection i] at h
  simp only [map_neg, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul] at h
  linarith

/-- Coroot evaluation vanishes exactly when the vector is orthogonal to the root. -/
theorem RelativeRootReflectionData.coroot_eq_zero_iff
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : Vstar T) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 ↔
      B x ((1 : ℝ) ⊗ₜ[ℤ] α.val) = 0 := by
  have h := D.coroot_mul_form i B hB α x
  have hp := hB.2.1 _ (D.one_tmul_ne_zero i α)
  constructor
  · intro hz
    rw [hz, zero_mul] at h
    linarith
  · intro hz
    rw [hz, mul_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hp.ne'

/-- The usual coroot formula, on the full real character space. -/
theorem RelativeRootReflectionData.coroot_formula
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : Vstar T) :
    pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) =
      2 * B x ((1 : ℝ) ⊗ₜ[ℤ] α.val) /
        B ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) :=
  (eq_div_iff (hB.2.1 _ (D.one_tmul_ne_zero i α)).ne').mpr
    (D.coroot_mul_form i B hB α x)

/-- The sign of a coroot evaluation is the sign of the corresponding inner product. -/
theorem RelativeRootReflectionData.coroot_pos_iff
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : Vstar T) :
    0 < pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) ↔
      0 < B x ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  rw [D.coroot_formula i B hB]
  exact (div_pos_iff_of_pos_right (hB.2.1 _ (D.one_tmul_ne_zero i α))).trans
    (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2))

/-- Nonnegative coroot evaluation is equivalent to nonnegative root inner product. -/
theorem RelativeRootReflectionData.coroot_nonneg_iff
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (α : relativeRoots i) (x : Vstar T) :
    0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) ↔
      0 ≤ B x ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  rw [D.coroot_formula i B hB]
  have hp := hB.2.1 _ (D.one_tmul_ne_zero i α)
  rw [div_nonneg_iff]
  constructor
  · rintro (⟨hx, _⟩ | ⟨_, hn⟩) <;> linarith
  · intro hx
    exact Or.inl ⟨by linarith, hp.le⟩

/-- The coroot annihilator is the orthogonal complement of the selected root span. -/
theorem corootAnnihilator_eq_orthogonal
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (J : Set (characterLattice T)) (hJ : J ⊆ relativeRoots i) :
    corootAnnihilator i D J =
      B.orthogonal
        (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) := by
  ext x
  rw [mem_corootAnnihilator, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hx
    have hspan :
        Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J) ≤
          (B x).ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨α, hα, rfl⟩
      exact (D.coroot_eq_zero_iff i B hB ⟨α, hJ hα⟩ x).mp (hx _ hα)
    intro y hy
    rw [hB.1]
    exact hspan hy
  · intro hx α hα
    apply (D.coroot_eq_zero_iff i B hB α x).mpr
    rw [hB.1]
    exact hx _ (Submodule.subset_span ⟨α.val, hα, rfl⟩)

omit [IsAffineHom G.X.hom] in
/-- Restricted real rational characters are fixed by every actual Weyl element. -/
theorem relativeWeylFullRealAction_restrictionRange (w : relativeWeylGroup i)
    (x : ℝ ⊗[ℤ] rationalCharacters G) :
    relativeWeylFullRealAction i w (rationalCharacterRestrictReal i x) =
      rationalCharacterRestrictReal i x := by
  induction w using Quotient.inductionOn with
  | h n =>
    induction x using TensorProduct.inductionOn with
    | tmul r χ =>
      change r ⊗ₜ[ℤ] weylAction i n (torusCharacterRestrict i χ) =
        r ⊗ₜ[ℤ] torusCharacterRestrict i χ
      rw [weylAction_torusCharacterRestrict]
    | add x y hx hy => simp only [map_add, hx, hy]

include D in
/-- Restricted rational characters are orthogonal to each actual root. -/
theorem RelativeRootReflectionData.restrictedCharacter_orthogonal
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (x : ℝ ⊗[ℤ] rationalCharacters G) (α : relativeRoots i) :
    B (rationalCharacterRestrictReal i x) ((1 : ℝ) ⊗ₜ[ℤ] α.val) = 0 := by
  have h := hB.2.2 (QuotientGroup.mk (D.representative α))
    (rationalCharacterRestrictReal i x) ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  rw [relativeWeylFullRealAction_restrictionRange, D.real_reflection_self i, map_neg] at h
  linarith

/-- Restricted rational characters annihilate all the supplied coroots. -/
theorem RelativeRootReflectionData.restrictedCharacter_coroot
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    (x : ℝ ⊗[ℤ] rationalCharacters G) (α : relativeRoots i) :
    pair T (rationalCharacterRestrictReal i x) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 :=
  (D.coroot_eq_zero_iff i B hB α _).mpr (D.restrictedCharacter_orthogonal i B hB x α)

include D in
/-- The restricted real group characters are orthogonal to the entire relative root span. -/
theorem restrictionRange_orthogonal_rootSpan
    (B : LinearMap.BilinForm ℝ (Vstar T)) (hB : IsWeylInvariantInnerProduct i B)
    {x y : Vstar T} (hx : x ∈ (rationalCharacterRestrictReal i).range)
    (hy : y ∈ relativeRootSpanReal i) : B x y = 0 := by
  obtain ⟨z, rfl⟩ := hx
  have hspan : relativeRootSpanReal i ≤ (B (rationalCharacterRestrictReal i z)).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨α, hα, rfl⟩
    exact D.restrictedCharacter_orthogonal i B hB z ⟨α, hα⟩
  exact hspan hy

end Langlands.GroupScheme
