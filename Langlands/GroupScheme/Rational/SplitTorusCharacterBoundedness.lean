import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.GaloisPointRational
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedTransport

/-! # Algebraic bounds from unit split-torus coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

variable {K : Type u} [Field K] [ValuativeRel K]
  (I : Type u) [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The rational points whose actual split coordinates all have valuation one. -/
def unitCoordinateLocus :
    Set (rationalPoints (splitTorus (Spec (CommRingCat.of K)) I)) :=
  {p | ∀ i, ValuativeRel.valuation K
    (affinePointsEquiv I (𝟙 (Spec (CommRingCat.of K))) p i : K) = 1}

omit [DecidableEq I] in
private theorem valuation_exponentValue_eq_one (t : I → Kˣ)
    (ht : ∀ i, ValuativeRel.valuation K (t i : K) = 1) (m : I → ℤ) :
    ValuativeRel.valuation K
      (exponentValue I t (Multiplicative.ofAdd m) : K) = 1 := by
  change ValuativeRel.valuation K (↑(∏ i, t i ^ m i) : K) = 1
  simp only [Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, ht, one_zpow,
    Finset.prod_const_one]

/-- The common unit-coordinate locus of a split torus is algebraically bounded over any
valuative field. No completeness or residue-field hypothesis is used. -/
theorem isAlgebraicallyBounded_of_unitCoordinates
    (B : Set (rationalPoints (splitTorus (Spec (CommRingCat.of K)) I)))
    (hB : ∀ p ∈ B, ∀ i,
      ValuativeRel.valuation K
        (affinePointsEquiv I (𝟙 (Spec (CommRingCat.of K))) p i : K) = 1) :
    letI : IsAffineHom (splitTorus (Spec (CommRingCat.of K)) I).X.hom :=
      isAffineHom_splitTorus _ _
    letI : IsAffine (splitTorus (Spec (CommRingCat.of K)) I).X.left :=
      isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of K)) I).X.hom
    IsAlgebraicallyBounded K (splitTorus (Spec (CommRingCat.of K)) I).X B := by
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of K)) I).X.hom :=
    isAffineHom_splitTorus _ _
  let : IsAffine (splitTorus (Spec (CommRingCat.of K)) I).X.left :=
    isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of K)) I).X.hom
  let t (p : B) : I → Kˣ :=
    algebraPointsEquiv (R := CommRingCat.of K) I K
      (GaloisPointComparison.rationalCoeffEquiv K _ p.val)
  have ht (p : B) (i : I) : ValuativeRel.valuation K (t p i : K) = 1 := by
    have h := hB p.val p.property i
    have heq : t p i = affinePointsEquiv I (𝟙 (Spec (CommRingCat.of K))) p.val i := by
      apply Units.ext
      change
        (Gm.affinePointsEquiv (R := CommRingCat.of K) _
          (GaloisPointComparison.rationalCoeffEquiv K _ p.val ≫
            (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of K))).toGrp) i).hom.hom) : K) =
        (Gm.affinePointsEquiv (R := CommRingCat.of K) _
          (p.val ≫
            (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of K))).toGrp) i).hom.hom) : K)
      rw [Gm.affinePointsEquiv_val, Gm.affinePointsEquiv_val,
        Gm.pointsEquiv_val, Gm.pointsEquiv_val,
        Over.comp_left, Over.comp_left,
        GaloisPointComparison.rationalCoeffEquiv_left]
      rfl
    rwa [heq]
  let e : B → AddMonoidAlgebra K (I → ℤ) →ₐ[K] K :=
    fun p => evaluateUnits (R := CommRingCat.of K) I (t p)
  have hbounded (a : AddMonoidAlgebra K (I → ℤ)) :
      a ∈ boundedEvaluationSubalgebra e := by
    induction a using AddMonoidAlgebra.induction_on with
    | of m =>
        refine ⟨1, one_ne_zero, fun p => ?_⟩
        change evaluateUnits I (t p) (AddMonoidAlgebra.single m 1) ≤ᵥ (1 : K)
        rw [evaluateUnits_single, map_one, one_mul]
        exact (ValuativeRel.valuation K).vle_iff_le.mpr
          (valuation_exponentValue_eq_one I (t p) (ht p) m).le
    | add a b ha hb => exact (boundedEvaluationSubalgebra e).add_mem ha hb
    | smul r a ha => exact (boundedEvaluationSubalgebra e).smul_mem ha r
  intro f
  let a : AddMonoidAlgebra K (I → ℤ) :=
    (splitTorus (Spec (CommRingCat.of K)) I).affinePointEvaluation
      (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ)))
      (universalPoint (R := CommRingCat.of K) I) f
  obtain ⟨b, hb, h⟩ := hbounded a
  refine ⟨b, hb, fun p hp => ?_⟩
  have heval : rationalPointAlgebraHom K _ p f = e ⟨p, hp⟩ a := by
    have hpoint : rationalPointAlgebraHom K _ p f =
        (splitTorus (Spec (CommRingCat.of K)) I).affinePointEvaluation
          (CommAlgCat.of K K)
          (GaloisPointComparison.rationalCoeffEquiv K _ p) f := by
      rw [GaloisPointComparison.rationalCoeffEquiv_eq]
      exact affineSchemePointEquiv_apply_eq_evaluation
        (splitTorus (Spec (CommRingCat.of K)) I) _ f
    rw [hpoint]
    change _ = (CommAlgCat.ofHom
      (evaluateUnits (R := CommRingCat.of K) I (t ⟨p, hp⟩)))
        ((splitTorus (Spec (CommRingCat.of K)) I).affinePointEvaluation
          (CommAlgCat.of K (AddMonoidAlgebra K (I → ℤ)))
          (universalPoint (R := CommRingCat.of K) I) f)
    rw [← GroupScheme.affinePointEvaluation_map]
    change _ = (splitTorus (Spec (CommRingCat.of K)) I).affinePointEvaluation
      (CommAlgCat.of K K)
      (Lie.affineMap _ (evaluateUnits (R := CommRingCat.of K) I (t ⟨p, hp⟩))
        (universalPoint (R := CommRingCat.of K) I)) f
    dsimp only [t]
    rw [universalPoint_evaluateUnits, MulEquiv.symm_apply_apply]
  rw [heval]
  exact h ⟨p, hp⟩

end Langlands.GroupScheme.splitTorus
