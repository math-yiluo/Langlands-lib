import Langlands.BruhatTits.Cartan.CentralizerValuation
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.Global.CharacterRestrictionRealDual

/-! # Real evaluation of actual character restriction to a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.GroupScheme

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] {S : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A real character `r ⊗ χ` pairs with a real cocharacter through the evaluation of `χ`. -/
theorem pair_tmul_eq_mul_eval (r : ℝ) (χ : characterLattice S) (v : RealTorusSpace.V S) :
    RealTorusSpace.pair S (r ⊗ₜ[ℤ] χ) v = r * RealTorusSpace.eval S χ v := by
  have h : (r ⊗ₜ[ℤ] χ : RealTorusSpace.Vstar S) = r • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, LinearMap.smul_apply, smul_eq_mul, RealTorusSpace.eval_eq_pair]

/-- On an actual split torus, a real cocharacter killed by every integral character is zero. -/
theorem eq_zero_of_eval_eq_zero (hS : IsSplitTorus S.toGrp) {v : RealTorusSpace.V S}
    (hv : ∀ χ : characterLattice S, RealTorusSpace.eval S χ v = 0) : v = 0 := by
  have hp := RealTorusSpace.isPerfPair_of_isSplitTorus hS
  apply hp.bijective_right.injective
  rw [map_zero]
  apply TensorProduct.AlgebraTensorModule.ext
  intro r χ
  rw [LinearMap.flip_apply, pair_tmul_eq_mul_eval, hv χ, mul_zero, LinearMap.zero_apply]

/-- On an actual split torus, every additive real functional on the integral characters is
evaluation at a real cocharacter. -/
theorem exists_eval_eq (hS : IsSplitTorus S.toGrp) (ℓ : characterLattice S →+ ℝ) :
    ∃ v : RealTorusSpace.V S, ∀ χ : characterLattice S, RealTorusSpace.eval S χ v = ℓ χ := by
  have hp := RealTorusSpace.isPerfPair_of_isSplitTorus hS
  let φ : RealTorusSpace.Vstar S →ₗ[ℝ] ℝ :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton ℝ (characterLattice S →ₗ[ℤ] ℝ) ℓ.toIntLinearMap)
  obtain ⟨v, hv⟩ := hp.bijective_right.surjective φ
  refine ⟨v, fun χ => ?_⟩
  have h := LinearMap.congr_fun hv ((1 : ℝ) ⊗ₜ[ℤ] χ)
  rw [LinearMap.flip_apply, pair_tmul_eq_mul_eval, one_mul] at h
  rw [h]
  change (1 : ℝ) • ℓ χ = ℓ χ
  rw [one_smul]

/-- For the identity of an actual split torus, restriction evaluation identifies its real
cocharacter space with the real dual of its rational characters. -/
theorem restrictionEvaluation_id_bijective (hS : IsSplitTorus S.toGrp) :
    Function.Bijective (restrictionEvaluation (𝟙 S.toGrp)) := by
  have hres : ∀ (v : RealTorusSpace.V S) (ψ : rationalCharacters S.toGrp),
      restrictionEvaluation (𝟙 S.toGrp) v ψ =
        RealTorusSpace.eval S (rationalCharacters.equivCharacterLattice S ψ) v := by
    intro v ψ
    rw [restrictionEvaluation_apply, characterRestriction, AddMonoidHom.comp_apply,
      characterRestrict_id, AddMonoidHom.id_apply]
    rfl
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply eq_zero_of_eval_eq_zero hS
    intro χ
    have h := DFunLike.congr_fun hv ((rationalCharacters.equivCharacterLattice S).symm χ)
    rwa [hres, AddEquiv.apply_symm_apply] at h
  · intro ℓ
    obtain ⟨v, hv⟩ := exists_eval_eq hS
      (ℓ.comp (rationalCharacters.equivCharacterLattice S).symm.toAddMonoidHom)
    refine ⟨v, AddMonoidHom.ext fun ψ => ?_⟩
    rw [hres, hv]
    simp

variable {Z : GroupScheme (Spec (CommRingCat.of F))}

/-- Restriction evaluation along `s` is restriction evaluation for the torus itself, followed by
the actual covariant map of real character duals. -/
theorem restrictionEvaluation_eq_realCharacterDualMap (s : S.toGrp ⟶ Z)
    (v : RealTorusSpace.V S) :
    restrictionEvaluation s v =
      Global.AdelicGroupPoints.realCharacterDualMap F S.toGrp Z s
        (restrictionEvaluation (𝟙 S.toGrp) v) := by
  apply AddMonoidHom.ext
  intro χ
  change RealTorusSpace.eval S (characterRestriction s χ) v =
    RealTorusSpace.eval S (characterRestriction (𝟙 S.toGrp) (characterRestrict s χ)) v
  rw [characterRestriction, characterRestriction, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, characterRestrict_id, AddMonoidHom.id_apply]

/-- **Real comparison.** If `S` is an actual split torus and restriction of rational characters
along `s : S → Z` is injective with finite-index range, then restriction evaluation
`V(S) → Hom(X^*(Z), ℝ)` is bijective. -/
theorem restrictionEvaluation_bijective (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (hinj : Function.Injective (characterRestrict s))
    [(characterRestrict s).range.FiniteIndex] :
    Function.Bijective (restrictionEvaluation s) := by
  have hcomp : (restrictionEvaluation s : RealTorusSpace.V S → rationalCharacters Z →+ ℝ) =
      (Global.AdelicGroupPoints.realCharacterDualRestrictionEquiv F Z S.toGrp s hinj) ∘
        (restrictionEvaluation (𝟙 S.toGrp)) := by
    funext v
    exact restrictionEvaluation_eq_realCharacterDualMap s v
  rw [hcomp]
  exact (Global.AdelicGroupPoints.realCharacterDualRestrictionEquiv F Z S.toGrp s
    hinj).bijective.comp (restrictionEvaluation_id_bijective hS)

/-- Restriction evaluation along `s`, bundled as a real-linear equivalence
`V(S) ≃ Hom(X^*(Z), ℝ)` under the hypotheses of `restrictionEvaluation_bijective`. -/
def restrictionEvaluationEquiv (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (hinj : Function.Injective (characterRestrict s))
    [(characterRestrict s).range.FiniteIndex] :
    RealTorusSpace.V S ≃ₗ[ℝ] (rationalCharacters Z →+ ℝ) :=
  LinearEquiv.ofBijective (restrictionEvaluation s) (restrictionEvaluation_bijective hS s hinj)

@[simp] theorem restrictionEvaluationEquiv_apply (hS : IsSplitTorus S.toGrp) (s : S.toGrp ⟶ Z)
    (hinj : Function.Injective (characterRestrict s))
    [(characterRestrict s).range.FiniteIndex] (v : RealTorusSpace.V S) :
    restrictionEvaluationEquiv hS s hinj v = restrictionEvaluation s v :=
  rfl

end Langlands.BruhatTits.Cartan
