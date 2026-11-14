import Langlands.Geometry.Building.KPWeilRestrictionCongruence
import Langlands.Geometry.Building.KPLocalCoordinateValuationComparison
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction

/-! # Geometric character congruence over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField Langlands.FieldTheory
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Algebra.SeparableTensor
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building.MaximalUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type u) [Field E] [Algebra (inertiaFixedField F) E]
  [FiniteDimensional (inertiaFixedField F) E]
  [Algebra.IsSeparable (inertiaFixedField F) E]
  (hH : HenselianLocalRing (valuation F).valuationSubring)

/-- Every geometric embedding preserves the exact normalized coordinate valuation. -/
theorem coordinateEmbedding_preserves_value
    (τ : E →ₐ[inertiaFixedField F] SeparableClosure F) (x : E) :
    algebraicExtensionAddValuation F (SeparableClosure F) (τ x) =
      henselianSeparableAddValuation (valuation F) hH E x :=
  (henselianSeparableAddValuation_eq_geometric F hH τ x).symm

/-- Normalized coordinate congruence maps to all geometric character congruences. -/
def henselianWeilUnitCongruenceHom (r : ℝ≥0) :
    addValuationUnitFiltration (henselianSeparableAddValuation (valuation F) hH E) r →*
      characterCongruence (algebraicExtensionAddValuation F (SeparableClosure F))
        (baseChanged (inertiaFixedField F) (SeparableClosure F)
          (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) E)) r :=
  weilGm_unitCongruenceHom (inertiaFixedField F) E (SeparableClosure F)
    (embeddingEvaluationStatement (inertiaFixedField F) E (SeparableClosure F)
      (WeilGm.separable_minpoly_splits (inertiaFixedField F) E (SeparableClosure F)))
    (henselianSeparableAddValuation (valuation F) hH E)
    (algebraicExtensionAddValuation F (SeparableClosure F))
    (coordinateEmbedding_preserves_value F E hH) r

@[simp] theorem henselianWeilUnitCongruenceHom_coe (r : ℝ≥0)
    (t : addValuationUnitFiltration (henselianSeparableAddValuation (valuation F) hH E) r) :
    (henselianWeilUnitCongruenceHom F E hH r t :
      rationalPoints (baseChanged (inertiaFixedField F) (SeparableClosure F)
        (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) E))) =
      WeilGm.extendedUnitPoint (inertiaFixedField F) E (SeparableClosure F) t.val := rfl

/-- A positive coordinate difference bound implies every required geometric character bound. -/
theorem weilGm_geometricCharacter_bound
    {r : ℝ≥0} (hr : 0 < r) (t : Eˣ)
    (ht : ((r : ℝ) : WithTop ℝ) ≤
      henselianSeparableAddValuation (valuation F) hH E ((t : E) - 1))
    (χ : rationalCharacters
      (baseChanged (inertiaFixedField F) (SeparableClosure F)
        (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) E))) :
    ((r : ℝ) : WithTop ℝ) ≤ algebraicExtensionAddValuation F (SeparableClosure F)
      ((rationalCharacterEval χ
        (rationalExtend (inertiaFixedField F) (SeparableClosure F)
          (WeilGm.groupScheme (CommRingCat.of (inertiaFixedField F)) E)
          ((WeilGm.rationalUnitsEquiv (inertiaFixedField F) E).symm t)) :
            SeparableClosure F) - 1) :=
  weilGm_rationalCharacterEval_sub_one_le_of_pos
    (inertiaFixedField F) E (SeparableClosure F)
    (embeddingEvaluationStatement (inertiaFixedField F) E (SeparableClosure F)
      (WeilGm.separable_minpoly_splits (inertiaFixedField F) E (SeparableClosure F)))
    (henselianSeparableAddValuation (valuation F) hH E)
    (algebraicExtensionAddValuation F (SeparableClosure F))
    (coordinateEmbedding_preserves_value F E hH) hr t ht χ

end Langlands.Geometry.Building.MaximalUnramified
