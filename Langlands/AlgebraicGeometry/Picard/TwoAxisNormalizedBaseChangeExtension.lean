import Langlands.AlgebraicGeometry.Picard.TwoAxisBundleNormalization
import Langlands.AlgebraicGeometry.Picard.NoetherianValuationBundleExtension
import Langlands.AlgebraicGeometry.Picard.CartesianSelfProduct
import Langlands.AbelianScheme.LieBaseChange

/-! # Actual extensions with two trivial total-space axes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S T : Scheme.{u}} (A : AbelianScheme S) (b : T ⟶ S)

/-- An actual extension along the canonical self-product map, together with
ordinary trivializations of both axes of its total-space bundle. -/
structure TwoAxisTrivialExtensionData
    (D : LineBundle (mumfordProduct ((baseChange b).obj A)).left) where
  bundle : LineBundle (mumfordProduct A).left
  first : (Scheme.Modules.pullback (mumfordSection A)).obj bundle.obj ≅
    structureSheaf A.X.left
  second : (Scheme.Modules.pullback (twoAxisSecond A)).obj bundle.obj ≅
    structureSheaf A.X.left
  restrictionIso :
    ((LineBundle.pullback (mumfordProductBaseChangeMap A b)).obj bundle).obj ≅ D.obj

/-- Specialize ordinary normalization to the actual canonical base-change map. -/
def twoAxisNormalizedBaseChangeRestrictionIso
    (E : LineBundle (mumfordProduct A).left)
    (D : LineBundle (mumfordProduct ((baseChange b).obj A)).left)
    (e : ((LineBundle.pullback (mumfordProductBaseChangeMap A b)).obj E).obj ≅ D.obj)
    (α : (Scheme.Modules.pullback
      (mumfordSection ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left)
    (β : (Scheme.Modules.pullback
      (twoAxisSecond ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left) :
    ((LineBundle.pullback (mumfordProductBaseChangeMap A b)).obj
      (LineBundle.twoAxisNormalizedBundle pullbackTensorComparisonIsIso A E)).obj ≅
        D.obj := by
  let B := (baseChange b).obj A
  let f : B.X.left ⟶ A.X.left := pullback.fst A.X.hom b
  have w : f ≫ A.X.hom = B.X.hom ≫ b := pullback.condition
  have hu : unitSection B ≫ f = b ≫ unitSection A :=
    Langlands.GroupScheme.identitySection_baseChange_fst b A.toGrp
  exact LineBundle.twoAxisNormalizedBundleRestrictionIso
    pullbackTensorComparisonIsIso A B (mumfordProductBaseChangeMap A b) f
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    (mumfordSection_cartesianMumfordProductMap B A f b w hu)
    (twoAxisSecond_cartesianMumfordProductMap B A f b w hu) E D e α β

/-- Correct an existing actual extension so that its total-space axes are
trivial, retaining an actual restriction isomorphism to the original bundle. -/
def twoAxisTrivialExtensionOfExtension
    (E : LineBundle (mumfordProduct A).left)
    (D : LineBundle (mumfordProduct ((baseChange b).obj A)).left)
    (e : ((LineBundle.pullback (mumfordProductBaseChangeMap A b)).obj E).obj ≅ D.obj)
    (α : (Scheme.Modules.pullback
      (mumfordSection ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left)
    (β : (Scheme.Modules.pullback
      (twoAxisSecond ((baseChange b).obj A))).obj D.obj ≅
        structureSheaf ((baseChange b).obj A).X.left) :
    TwoAxisTrivialExtensionData A b D where
  bundle := LineBundle.twoAxisNormalizedBundle pullbackTensorComparisonIsIso A E
  first := LineBundle.twoAxisNormalizedBundleFirst pullbackTensorComparisonIsIso A E
  second := LineBundle.twoAxisNormalizedBundleSecond pullbackTensorComparisonIsIso A E
  restrictionIso := twoAxisNormalizedBaseChangeRestrictionIso A b E D e α β

variable (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
  [IsNoetherianRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (A₀ : AbelianScheme (Spec (CommRingCat.of R)))
  (D₀ : LineBundle (mumfordProduct
    ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A₀)).left)

/-- Two-axis-trivial generic bundles over a Noetherian valuation domain admit
actual extensions with both total-space axes trivial. -/
def noetherianValuationRingTwoAxisNormalizedExtension
    (hα : Nonempty ((Scheme.Modules.pullback
      (mumfordSection
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A₀))).obj
          D₀.obj ≅ structureSheaf
            ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A₀).X.left))
    (hβ : Nonempty ((Scheme.Modules.pullback
      (twoAxisSecond
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A₀))).obj
          D₀.obj ≅ structureSheaf
            ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj A₀).X.left)) :
    TwoAxisTrivialExtensionData A₀
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) D₀ :=
  let extension := noetherianValuationRingSelfProductExtension R K A₀ D₀
  twoAxisTrivialExtensionOfExtension A₀
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) extension.1 D₀ extension.2
    (Classical.choice hα) (Classical.choice hβ)

end Langlands.AbelianScheme
