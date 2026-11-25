/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData

import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank

/-! # The geometric input to analytic integral matrix charts -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem integralMatrixFunctions_eq_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    {n t : ℕ}
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (ha : ∀ i j x, integralMatrixFunctions ℓ E X
      (chartComparison X (continuousIntegers ℓ E)) a i j x = 0) : a = 0 := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let O := continuousIntegers ℓ E
  let e := chartComparison X O
  let F := (Mod.comapEquivalenceOfIsIso (inv e)).functor
  let jR := Mod.regularIsoOfIsIso e
  apply biproduct.hom_ext'
  intro j
  apply biproduct.hom_ext
  intro i
  let p : Mod.regular R ⟶ Mod.regular R :=
    biproduct.ι (fun _ : Fin n ↦ Mod.regular R) j ≫ a ≫
      biproduct.π (fun _ : Fin t ↦ Mod.regular R) i
  let p' := jR.inv ≫ F.map p ≫ jR.hom
  have hp' : p' = 0 := by
    apply regularCoefficient_injective X O
    ext x
    change (integralMatrixFunctions ℓ E X e a i j x).val = 0
    exact congrArg Subtype.val (ha i j x)
  have hp : p = 0 := by
    apply F.map_injective
    rw [Functor.map_zero]
    have hh : F.map p = jR.hom ≫ p' ≫ jR.inv := by
      simp only [p', Category.assoc, Iso.hom_inv_id_assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [hh, hp', Limits.zero_comp, Limits.comp_zero]
  simpa only [Limits.comp_zero, Limits.zero_comp, Category.assoc] using hp

private theorem matrix_eq_zero_of_rank_zero {E : Type} [Field E]
    {n t : ℕ} (M : Matrix (Fin t) (Fin n) E) (h : M.rank = 0) : M = 0 := by
  have hr : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  have hl : M.mulVecLin = 0 := LinearMap.range_eq_bot.mp hr
  ext i j
  have hh := congrArg (fun f : (Fin n → E) →ₗ[E] (Fin t → E) ↦
    f (Pi.single j 1) i) hl
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    LinearMap.zero_apply, Pi.zero_apply, Matrix.zero_apply] using hh

/-- A point where the continuous matrix vanishes has a vanishing open neighborhood,
after refining the supplied free rational-cokernel cover.

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1),
and exact geometric-field evaluation (Example 4.1.10).
(auxiliary; not a blueprint node)

Proof: choose the cover supplied by the hypothesis and a free basis of the rational
cokernel on each member, of rank q. Pull the rational cokernel presentation and this
basis to an algebraically closed residue field at each point. Exact final-object
evaluation preserves cokernels and finite free objects and identifies the matrix
coefficients with their point values. Thus the evaluated matrix rank is t-q at every
point. If all integral entries vanish at one point, their field images vanish, the
matrix rank is zero, and q=t. It follows that every entry vanishes at every point of
that member. The canonical continuous realization is faithful on regular module
endomorphisms (each is multiplication by its value at 1); finite biproduct
extensionality therefore makes the pulled-back morphism zero. Its pullback to any
open neighborhood is zero by functoriality and the composition comparison. Take the
whole member as neighborhood. Empty members contribute no points; rank-zero source
or target has zero matrix directly. -/
theorem integralMatrix_zero_neighborhood (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k (x : V.X k),
      (∀ i j, integralMatrixPullbackFunctions ℓ E (V.f k) a i j x = 0) →
        ∃ U : (V.X k).Opens, x ∈ U ∧
          (integralMatrixPullback ℓ E (U.ι ≫ V.f k)).map a = 0 := by
  classical
  obtain ⟨V, hV⟩ := integralMatrix_pointwise_rank ℓ E n t X a hC
  refine ⟨V, fun k x hx ↦ ?_⟩
  have hxmat : (fun i j ↦
      (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val) =
        (0 : Matrix (Fin t) (Fin n) E) := by
    ext i j
    exact congrArg Subtype.val (hx i j)
  have hall (y : V.X k) (i : Fin t) (j : Fin n) :
      integralMatrixPullbackFunctions ℓ E (V.f k) a i j y = 0 := by
    have hr : Matrix.rank (fun i j ↦
        (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val) = 0 := by
      rw [hV k y x, hxmat, Matrix.rank_zero]
    have hm := matrix_eq_zero_of_rank_zero _ hr
    apply Subtype.ext
    exact congrArg (fun M : Matrix (Fin t) (Fin n) E ↦ M i j) hm
  let U : (V.X k).Opens := ⊤
  refine ⟨U, trivial, ?_⟩
  let g := U.ι ≫ V.f k
  have hm : integralMatrixPullbackMap ℓ E g a = 0 := by
    apply integralMatrixFunctions_eq_zero
    intro i j z
    have hc : integralMatrixPullbackFunctions ℓ E g a i j z = 0 := by
      rw [integralMatrixFunctions_pullback]
      exact hall (U.ι z) i j
    simpa only [integralMatrixPullbackFunctions] using hc
  let eA := integralFiniteFreePullbackIso ℓ E g n
  let eB := integralFiniteFreePullbackIso ℓ E g t
  have hh := congrArg (fun b ↦ eA.hom ≫ b ≫ eB.inv) hm
  simpa only [integralMatrixPullbackMap, eA, eB, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
    Limits.comp_zero, Limits.zero_comp] using hh

end AlgebraicGeometry.ProEtale.CondensedRing
