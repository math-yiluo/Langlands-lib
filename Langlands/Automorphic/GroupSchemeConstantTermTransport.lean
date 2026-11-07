import Langlands.Automorphic.GroupSchemeAmbientFunctorial
import Langlands.Automorphic.GroupSchemeConstantTermConsequences
import Langlands.Global.AdelicSubgroupQuotientTransport

/-! # Constant-term transport under actual group-scheme isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]
  (e : G ≅ H) (V : Langlands.GroupScheme.SubgroupFunctor H)

/-- The actual descended integrands commute with pullback and the constructed
subgroup-quotient isomorphism. -/
theorem constantTermIntegrand_continuousPullback
    (f : ContinuousRationalFunctions F H) (g : AdelicGroupPoints F G) :
    constantTermIntegrand F G (V.comap e.hom) (continuousPullback F e.hom f) g =
      constantTermIntegrand F H V f (AdelicGroupPoints.map F G H e.hom g) ∘
        AdelicSubgroupPoints.rationalQuotientIso F e V := by
  funext q
  induction q using Quotient.inductionOn with
  | _ n =>
    exact congrArg f.val.val
      ((AdelicGroupPoints.map F G H e.hom).map_mul n.val g)

section CompactMeasure

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  [hV : IsClosed (AdelicSubgroupPoints.adelicPoints F H V :
    Set (AdelicGroupPoints F H))]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F H V)]

local instance constantTermTransportSourceClosed :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G (V.comap e.hom) :
      Set (AdelicGroupPoints F G)) :=
  AdelicSubgroupPoints.isClosed_adelicPoints_comap F e V

/-- Absolute convergence of corresponding integrands is equivalent. -/
theorem integrable_constantTermIntegrand_continuousPullback_iff
    (f : ContinuousRationalFunctions F H) (g : AdelicGroupPoints F G) :
    Integrable
      (constantTermIntegrand F G (V.comap e.hom) (continuousPullback F e.hom f) g)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (V.comap e.hom)) ↔
    Integrable
      (constantTermIntegrand F H V f (AdelicGroupPoints.map F G H e.hom g))
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V) := by
  rw [constantTermIntegrand_continuousPullback]
  exact AdelicSubgroupPoints.integrable_comp_rationalQuotientIso_iff F e V _

/-- The unchanged intrinsic normalized constant term commutes with pullback.
The preceding theorem records convergence separately. -/
theorem constantTerm_continuousPullback
    (f : ContinuousRationalFunctions F H) (g : AdelicGroupPoints F G) :
    constantTerm F G (V.comap e.hom)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (V.comap e.hom))
        (continuousPullback F e.hom f) g =
      constantTerm F H V (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)
        f (AdelicGroupPoints.map F G H e.hom g) := by
  unfold constantTerm
  rw [constantTermIntegrand_continuousPullback]
  exact AdelicSubgroupPoints.integral_comp_rationalQuotientIso F e V _

/-- Pullback identifies the original convergence conditions at every ambient argument. -/
theorem hasConvergentConstantTerm_continuousPullback_iff
    (f : ContinuousRationalFunctions F H) :
    HasConvergentConstantTerm F G (V.comap e.hom)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (V.comap e.hom))
        (continuousPullback F e.hom f) ↔
      HasConvergentConstantTerm F H V
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V) f := by
  constructor
  · intro hf y
    obtain ⟨g, rfl⟩ := (Langlands.GroupScheme.affinePointsIsoHomeomorph e
      (CommAlgCat.of F (AdeleRing (𝓞 F) F))).surjective y
    exact (integrable_constantTermIntegrand_continuousPullback_iff F e V f g).mp (hf g)
  · intro hf g
    exact (integrable_constantTermIntegrand_continuousPullback_iff F e V f g).mpr
      (hf (AdelicGroupPoints.map F G H e.hom g))

/-- Both convergence and vanishing transport, on the existing ambient carriers. -/
theorem hasVanishingConstantTerm_continuousPullback_iff
    (f : ContinuousRationalFunctions F H) :
    HasVanishingConstantTerm F G (V.comap e.hom)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G (V.comap e.hom))
        (continuousPullback F e.hom f) ↔
      HasVanishingConstantTerm F H V
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V) f := by
  constructor
  · rintro ⟨hf, hz⟩
    refine ⟨(hasConvergentConstantTerm_continuousPullback_iff F e V f).mp hf, ?_⟩
    intro y
    obtain ⟨g, rfl⟩ := (Langlands.GroupScheme.affinePointsIsoHomeomorph e
      (CommAlgCat.of F (AdeleRing (𝓞 F) F))).surjective y
    exact (constantTerm_continuousPullback F e V f g).symm.trans (hz g)
  · rintro ⟨hf, hz⟩
    refine ⟨(hasConvergentConstantTerm_continuousPullback_iff F e V f).mpr hf, ?_⟩
    intro g
    exact (constantTerm_continuousPullback F e V f g).trans
      (hz (AdelicGroupPoints.map F G H e.hom g))

/-- Pullback restricts to a linear equivalence of the existing convergent,
zero-constant-term subspaces for the corresponding actual subgroup functors. -/
def vanishingConstantTermPullbackEquiv :
    (vanishingConstantTermSubrepresentation F H V
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)).toSubmodule ≃ₗ[ℂ]
    (vanishingConstantTermSubrepresentation F G (V.comap e.hom)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
        (V.comap e.hom))).toSubmodule := by
  let source := (vanishingConstantTermSubrepresentation F G (V.comap e.hom)
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
      (V.comap e.hom))).toSubmodule
  let target := (vanishingConstantTermSubrepresentation F H V
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)).toSubmodule
  let E := continuousPullbackEquiv F e
  have h : target = source.comap E.toLinearMap := by
    ext f
    exact (hasVanishingConstantTerm_continuousPullback_iff F e V f).symm
  exact (LinearEquiv.ofEq target (source.comap E.toLinearMap) h).trans
    (E.ofSubmodule' source)

@[simp]
theorem vanishingConstantTermPullbackEquiv_apply
    (f : (vanishingConstantTermSubrepresentation F H V
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)).toSubmodule) :
    (vanishingConstantTermPullbackEquiv F e V f).val =
      continuousPullback F e.hom f.val := rfl

@[simp]
theorem vanishingConstantTermPullbackEquiv_symm_apply
    (f : (vanishingConstantTermSubrepresentation F G (V.comap e.hom)
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
        (V.comap e.hom))).toSubmodule) :
    ((vanishingConstantTermPullbackEquiv F e V).symm f).val =
      continuousPullback F e.inv f.val := rfl

/-- The restricted equivalence preserves the positive right actions along the
actual ambient adelic point isomorphism. -/
theorem vanishingConstantTermPullbackEquiv_rightAction
    (f : (vanishingConstantTermSubrepresentation F H V
      (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)).toSubmodule)
    (g : AdelicGroupPoints F G) :
    vanishingConstantTermPullbackEquiv F e V
        ((vanishingConstantTermSubrepresentation F H V
          (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F H V)).toRepresentation
            (AdelicGroupPoints.map F G H e.hom g) f) =
      (vanishingConstantTermSubrepresentation F G (V.comap e.hom)
        (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
          (V.comap e.hom))).toRepresentation g
            (vanishingConstantTermPullbackEquiv F e V f) := by
  apply Subtype.ext
  exact continuousPullback_rightAction F e.hom f.val g

end CompactMeasure

end Langlands.Automorphic.GroupSchemeFunctions
