import Langlands.Representation.Plancherel.ActualConjugateLeviIdentityLaw
import Langlands.Representation.Plancherel.ActualConjugateLeviComparisonRegularity

/-! # Composition of actual translated comparisons -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviCoherence

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact ActualCommonLeviTensor
open ActualCommonLeviCompactTensor ActualCommonLeviCoherence
open ActualConjugateLeviTwist ActualConjugateLeviFiberTransport
open ActualParabolicTranslation ActualParabolicUnitaryTranslation

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.parabolicLocallyCompact ActualCommonLeviV3.radicalLocallyCompact
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Cochar" => (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
set_option hygiene false in
local notation "Gpts" => RationalPoint F G.X

section Composition

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (s t : K)

set_option hygiene false in
local notation "sG" => (s : Gpts)
set_option hygiene false in
local notation "tG" => (t : Gpts)
set_option hygiene false in
local notation "stG" => ((s * t : K) : Gpts)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χt" => (χ ≫ (G.innerIso tG).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χts" => (χt ≫ (G.innerIso sG).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χst" => (χ ≫ (G.innerIso stG).hom)
set_option hygiene false in
local notation "At" => conjugateRepresentation χ tG A
set_option hygiene false in
local notation "Ats" => conjugateRepresentation χt sG At
set_option hygiene false in
local notation "Ast" => conjugateRepresentation χ stG A
set_option hygiene false in
local notation "zt" => ActualConjugateLeviV3.unitaryConjugateParameter χ tG
set_option hygiene false in
local notation "zts" => ActualConjugateLeviV3.unitaryConjugateParameter χt sG
set_option hygiene false in
local notation "zst" => ActualConjugateLeviV3.unitaryConjugateParameter χ stG

/-- The twice-conjugated target of a composition, with `s` and `t` viewed as
  points of the common compact subgroup. -/
private abbrev multiplicationTargetAt (R : ParabolicPresentation χst K) :
    ParabolicPresentation χts K :=
  multiplicationTarget χ sG tG R

/-- The canonical comparison from the twice-conjugated fiber to the fiber for
  the product point of the compact subgroup. -/
private abbrev multiplicationReturn (R : ParabolicPresentation χst K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χts Ats K (multiplicationTargetAt χ K s t R) (zts (zt z))).representation.Equiv
      (fiber χst Ast K R (zst z)).representation := by
  with_reducible_and_instances exact multiplicationTransport χ sG tG hG A K hK R z

/-- The multiplication transport has a parameter-independent value in the
  fixed compact charts. -/
private theorem multiplicationReturn_chartValue_const (R : ParabolicPresentation χst K)
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue (fun w => unitaryChart χts hG Ats K hK (multiplicationTargetAt χ K s t R) (zts (zt w)))
        (fun w => unitaryChart χst hG Ast K hK R (zst w))
        (fun w => (multiplicationReturn χ hG A K hK s t R w).toLinearMap) z =
      chartValue (fun w => unitaryChart χts hG Ats K hK (multiplicationTargetAt χ K s t R) (zts (zt w)))
        (fun w => unitaryChart χst hG Ast K hK R (zst w))
        (fun w => (multiplicationReturn χ hG A K hK s t R w).toLinearMap) z' := by
  with_reducible_and_instances
    exact multiplicationTransport_chartValue_const χ sG tG hG A K hK R z z'

/-- The multiplication transport preserves the published coefficient maps. -/
private theorem multiplicationReturn_coefficientMap (dts : LeviNormalization χts Ats)
    (dst : LeviNormalization χst Ast) (R : ParabolicPresentation χst K)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (y : fiber χts Ats K (multiplicationTargetAt χ K s t R) (zts (zt z))) :
    coefficientMap χst hG Ast dst K hK R (zst z) (multiplicationReturn χ hG A K hK s t R z y) =
      coefficientMap χts hG Ats dts K hK (multiplicationTargetAt χ K s t R) (zts (zt z)) y := by
  with_reducible_and_instances
    exact anchorChange_coefficientMap (conjugationAnchor_mul χ sG tG).symm hG hK R Ast Ats
      dst dts (zst z) (zts (zt z)) (multiplicationTransport χ sG tG hG A K hK R z)
      (multiplicationInducingEquiv χ sG tG A z) (multiplicationTransport_eq χ sG tG hG A K hK R z) y

/-- The composite of the comparisons for `t` and `s`, with the multiplication
  transport, agrees with the comparison for `s * t` at every unitary parameter. -/
private theorem composition_at (d : LeviNormalization χ A) (dt : LeviNormalization χt At)
    (dts : LeviNormalization χts Ats) (dst : LeviNormalization χst Ast)
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χt K) (R : ParabolicPresentation χst K)
    (Tt : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ tG A K K P Q)
    (Ts : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χt sG At K K Q
      (multiplicationTargetAt χ K s t R))
    (Tst : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ stG A K K P R)
    (ht : IsActualComparison χ hG A K hK t d dt P Q (by with_reducible_and_instances exact Tt))
    (hs : IsActualComparison χt hG At K hK s dt dts Q (multiplicationTargetAt χ K s t R)
      (by with_reducible_and_instances exact Ts))
    (hst : IsActualComparison χ hG A K hK (s * t) d dst P R (by with_reducible_and_instances exact Tst))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    TransportedComposite (multiplicationReturn χ hG A K hK s t R z) (Ts (zt z)) (Tt z v) (Tst z v) := by
  have htfin := actualComparison_locallyFinite χ hG A K hK t P d dt Q Tt ht
  have hsfin := actualComparison_locallyFinite χt hG At K hK s Q dt dts
    (multiplicationTargetAt χ K s t R) Ts hs
  have hsfin' := isLocallyFiniteFamily_chartValue_reindex
    (unitaryChart χt hG At K hK Q)
    (fun w => unitaryChart χts hG Ats K hK (multiplicationTargetAt χ K s t R) (zts w))
    (fun w => (Ts w).toLinearMap) hsfin zt (zt).continuous
  have hstfin := actualComparison_locallyFinite χ hG A K hK (s * t) P d dst R Tst hst
  have hcoef (w : unitaryUnramifiedCharacters (normCharacters χ)) (x : fiber χ A K P w) :
      coefficientMap χst hG Ast dst K hK R (zst w)
          (multiplicationReturn χ hG A K hK s t R w (Ts (zt w) (Tt w x))) =
        coefficientMap χ hG A d K hK P w x :=
    (multiplicationReturn_coefficientMap χ hG A K hK s t dts dst R w _).trans
      ((actualComparison_coefficientMap χt hG At K hK s Q dt dts (multiplicationTargetAt χ K s t R)
        Ts hs (zt w) (Tt w x)).trans (actualComparison_coefficientMap χ hG A K hK t P d dt Q Tt ht w x))
  have hinj (w : unitaryUnramifiedCharacters (normCharacters χ))
      (hw : w ∈ {w | Function.Injective (coefficientMap χ hG A d K hK P w)}) :
      Function.Injective (coefficientMap χ hG A d K hK P w) := hw
  have hsurj (w : unitaryUnramifiedCharacters (normCharacters χ)) :
      Function.Surjective (Tst w) :=
    (actualComparison_bijective χ hG A K hK (s * t) P d dst R Tst hst w).2
  have heq := by
    with_reducible_and_instances
      exact eq_of_chain (unitaryChart χ hG A K hK P)
        (fun w => unitaryChart χt hG At K hK Q (zt w))
        (fun w => unitaryChart χts hG Ats K hK (multiplicationTargetAt χ K s t R) (zts (zt w)))
        (fun w => unitaryChart χst hG Ast K hK R (zst w))
        (fun w => coefficientMap χ hG A d K hK P w) (fun w => coefficientMap χst hG Ast dst K hK R (zst w))
        (fun w => (Tt w).toLinearMap) (fun w => (Ts (zt w)).toLinearMap)
        (fun w => (multiplicationReturn χ hG A K hK s t R w).toLinearMap) (fun w => (Tst w).toLinearMap)
        hcoef (actualComparison_coefficientMap χ hG A K hK (s * t) P d dst R Tst hst) hsurj
        (coefficientMap_injective_dense χ hG A K hK d P) hinj
        htfin hsfin' (multiplicationReturn_chartValue_const χ hG A K hK s t R) hstfin.weaklyContinuous z v
  exact (transportedComposite_iff _ _ _ _).mpr heq

/-- The certified comparisons compose in the order `s * t`, through the
  canonical comparison of the two target fibers. -/
theorem compositionLaw (d : LeviNormalization χ A) : CompositionLaw χ hG A K hK d := by
  intro s t dt dts dst P Q R Tt Ts Tst z v
  with_reducible_and_instances
    exact composition_at χ hG A K hK s t d dt dts dst P Q R Tt.val Ts.val Tst.val
      Tt.property Ts.property Tst.property z v

end Composition

end Langlands.Plancherel.ActualConjugateLeviCoherence
