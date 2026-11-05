import Langlands.Automorphic.GroupSchemeParabolicCuspidal
import Langlands.Global.AdelicSubgroupHaarMeasure

/-! # Mass-one measures for the intrinsic rational parabolic radical family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- The actual adelic image of any represented parabolic radical is closed. -/
theorem IsRationalParabolicRadical.isClosed_adelicPoints
    {P U : SubgroupFunctor G} (hU : IsRationalParabolicRadical P U) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) := by
  obtain ⟨P₀, U₀, p, r, hp, _, hr, rfl⟩ := hU
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : IsAffineHom P₀.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  let : IsAffineHom U₀.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : IsAffine U₀.X.left := isAffine_of_isAffineHom U₀.X.hom
  let : IsClosedImmersion (r ≫ p).hom.hom.left := by
    change IsClosedImmersion (r.hom.hom.left ≫ p.hom.hom.left)
    infer_instance
  exact AdelicSubgroupPoints.isClosed_adelicPoints_range F G (r ≫ p)

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)

instance isClosed_properRationalParabolicRadicalAdelicPoints
    (P : ProperRationalParabolic G) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G
      (properRationalParabolicRadicals hPD hG P) : Set (AdelicGroupPoints F G)) :=
  (rationalParabolicRadical_spec hPD hG P.val).isClosed_adelicPoints F G

instance properRationalParabolicRadicalLocallyCompactSpace
    (P : ProperRationalParabolic G) :
    LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G
      (properRationalParabolicRadicals hPD hG P)) :=
  (isClosed_properRationalParabolicRadicalAdelicPoints F G hPD hG P).locallyCompactSpace

instance properRationalParabolicRadicalQuotientCompactSpace
    (P : ProperRationalParabolic G) :
    CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)) :=
  compactSpace_properRationalParabolicRadicalQuotient F G hPD hG P

instance properRationalParabolicRadicalQuotientBorelSpace
    (P : ProperRationalParabolic G) :
    BorelSpace (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)) :=
  AdelicSubgroupPoints.rationalQuotientBorelSpace F G _

/-- Haar on each actual adelic radical subgroup, normalized by its actual quotient mass. -/
def properParabolicHaarMeasure (P : ProperRationalParabolic G) :
    Measure (AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P)) :=
  AdelicSubgroupPoints.normalizedHaarMeasure F G _

/-- The intrinsic mass-one quotient measure for every proper rational parabolic radical. -/
def properParabolicQuotientMeasure (P : ProperRationalParabolic G) :
    Measure (AdelicSubgroupPoints.RationalQuotient F G
      (properRationalParabolicRadicals hPD hG P)) :=
  AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G _

instance properParabolicQuotientMeasure_isProbabilityMeasure (P : ProperRationalParabolic G) :
    IsProbabilityMeasure (properParabolicQuotientMeasure F G hPD hG P) :=
  AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G _

/-- The all-proper-parabolic vanishing space now uses the actual mass-one measure family. -/
def normalizedParabolicCuspidalSubrepresentation :
    Subrepresentation (continuousRightAction F G) :=
  parabolicCuspidalSubrepresentation F G hPD hG (properParabolicQuotientMeasure F G hPD hG)

/-- No measure choice or convergence assumption is supplied by a continuous function. -/
theorem hasConvergentNormalizedParabolicConstantTerm (P : ProperRationalParabolic G)
    (f : ContinuousRationalFunctions F G) :
    HasConvergentConstantTerm F G (properRationalParabolicRadicals hPD hG P)
      (properParabolicQuotientMeasure F G hPD hG P) f :=
  hasConvergentProperParabolicConstantTerm F G hPD hG
    (properParabolicQuotientMeasure F G hPD hG) P f

theorem mem_normalizedParabolicCuspidalSubrepresentation_iff
    (f : ContinuousRationalFunctions F G) :
    f ∈ normalizedParabolicCuspidalSubrepresentation F G hPD hG ↔
      ∀ (P : ProperRationalParabolic G) (g : AdelicGroupPoints F G),
        constantTerm F G (properRationalParabolicRadicals hPD hG P)
          (properParabolicQuotientMeasure F G hPD hG P) f g = 0 :=
  mem_parabolicCuspidalSubrepresentation_iff F G hPD hG
    (properParabolicQuotientMeasure F G hPD hG) f

section RightInvariant

variable (P : ProperRationalParabolic G)
  [(Measure.haar : Measure (AdelicSubgroupPoints.adelicPoints F G
    (properRationalParabolicRadicals hPD hG P))).IsMulRightInvariant]

/-- Exact counting-measure Weil compatibility retains analytic subgroup right invariance. -/
theorem properParabolicQuotientMeasure_isCompatible :
    Langlands.QuotientIntegration.IsCompatible
      (AdelicSubgroupPoints.rationalSubgroup F G (properRationalParabolicRadicals hPD hG P))
      (properParabolicHaarMeasure F G hPD hG P) Measure.count
      (properParabolicQuotientMeasure F G hPD hG P) :=
  AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isCompatible F G _

theorem normalizedParabolicConstantTerm_subgroup_mul
    (f : ContinuousRationalFunctions F G)
    (n : AdelicSubgroupPoints.adelicPoints F G (properRationalParabolicRadicals hPD hG P))
    (g : AdelicGroupPoints F G) :
    constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f ((n : AdelicGroupPoints F G) * g) =
      constantTerm F G (properRationalParabolicRadicals hPD hG P)
        (properParabolicQuotientMeasure F G hPD hG P) f g :=
  constantTerm_subgroup_mul F G _ _ f n
    (AdelicSubgroupPoints.measurePreserving_rightTranslate_normalizedRationalQuotientHaarMeasure
      F G _ n) g

end RightInvariant

end Langlands.Automorphic.GroupSchemeFunctions
