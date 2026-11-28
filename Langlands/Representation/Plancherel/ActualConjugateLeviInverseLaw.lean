import Langlands.Representation.Plancherel.ActualConjugateLeviIdentityLaw
import Langlands.Representation.Plancherel.ActualConjugateLeviComparisonRegularity

/-! # The inverse law for the actual translated comparison -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV uS uM uT

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

/-- A left inverse through the return transport gives both inverse equations
when the forward comparison is surjective. -/
private theorem transportedInverse_of_surjective {U : Type uS} {V V' : Type uM} {W W' : Type uT}
    (E : V → W) (S : U → V') (T : W' → U) (hT : Function.Surjective T)
    (hL : ∀ w, TransportedValue E (S (T w)) w) :
    TransportedInverse E S T := by
  refine ⟨fun w => ⟨T w, HEq.rfl, hL w⟩, fun u => ?_⟩
  obtain ⟨w, hw⟩ := hT u
  exact ⟨w, ⟨T w, heq_of_eq hw, hL w⟩, heq_of_eq hw⟩

section Inverse

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (g : K)

set_option hygiene false in
local notation "gG" => ((g : K) : Gpts)
set_option hygiene false in
local notation "gi" => ((g⁻¹ : K) : Gpts)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso gG).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χgi" => (χg ≫ (G.innerIso gi).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ gG A
set_option hygiene false in
local notation "Agi" => conjugateRepresentation χg gi Ag
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ gG
set_option hygiene false in
local notation "zgi" => ActualConjugateLeviV3.unitaryConjugateParameter χg gi
/-- The inverse-arrow target presentation, over the anchor conjugated by `g` and
then by the inverse point of the compact subgroup. -/
private abbrev inverseTargetAt (P : ParabolicPresentation χ K) : ParabolicPresentation χgi K :=
  inverseTarget χ gG P

/-- The inverse-arrow transport, written with the inverse point of the compact
subgroup. -/
abbrev inverseReturn (P : ParabolicPresentation χ K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χgi Agi K (inverseTargetAt χ K g P) (zgi (zg z))).representation.Equiv
      (fiber χ A K P z).representation := by
  with_reducible_and_instances exact inverseTransport χ gG hG A K hK P z

/-- The inverse-arrow transport has a parameter-independent value in the fixed
compact charts. -/
theorem inverseReturn_chartValue_const (P : ParabolicPresentation χ K)
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χgi hG K hK (inverseTargetAt χ K g P).cocharacter
          (inverseTargetAt χ K g P).centralizer_eq (inverseTargetAt χ K g P).iwasawa Agi
          (ActualCommonLeviV3.unitaryParameter χgi (zgi (zg z))))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (inverseReturn χ hG A K hK g P z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χgi hG K hK (inverseTargetAt χ K g P).cocharacter
          (inverseTargetAt χ K g P).centralizer_eq (inverseTargetAt χ K g P).iwasawa Agi
          (ActualCommonLeviV3.unitaryParameter χgi (zgi (zg z))))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (inverseReturn χ hG A K hK g P z).toLinearMap) z' := by
  with_reducible_and_instances
    exact inverseTransport_chartValue_const χ gG hG A K hK P z z'

/-- The inverse-arrow transport preserves the published coefficient maps. -/
theorem inverseReturn_coefficientMap (d : LeviNormalization χ A)
    (db : LeviNormalization χgi Agi) (P : ParabolicPresentation χ K)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (y : fiber χgi Agi K (inverseTargetAt χ K g P) (zgi (zg z))) :
    coefficientMap χ hG A d K hK P z (inverseReturn χ hG A K hK g P z y) =
      coefficientMap χgi hG Agi db K hK (inverseTargetAt χ K g P) (zgi (zg z)) y := by
  with_reducible_and_instances
    exact anchorChange_coefficientMap (conjugationAnchor_inv χ gG).symm hG hK P A
      (conjugateRepresentation (χ ≫ (G.innerIso gG).hom) gG⁻¹ Ag) d db z
      (ActualConjugateLeviV3.unitaryConjugateParameter (χ ≫ (G.innerIso gG).hom) gG⁻¹ (zg z))
      (inverseTransport χ gG hG A K hK P z) (inverseInducingEquiv χ gG A z)
      (inverseTransport_eq χ gG hG A K hK P z) y

set_option maxHeartbeats 800000 in
/-- The inverse comparison followed by the return transport is a left inverse
  to the forward comparison at every unitary parameter. -/
private theorem inverse_loop (d : LeviNormalization χ A)
    (dg : LeviNormalization χg Ag) (db : LeviNormalization χgi Agi)
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χg K)
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ gG A K K P Q)
    (S : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χg gi Ag K K Q
      (inverseTargetAt χ K g P))
    (hT : IsActualComparison χ hG A K hK g d dg P Q (by with_reducible_and_instances exact T))
    (hS : IsActualComparison χg hG Ag K hK g⁻¹ dg db Q (inverseTargetAt χ K g P)
      (by with_reducible_and_instances exact S))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    inverseReturn χ hG A K hK g P z (S (zg z) (T z v)) = v := by
  have hTfin := actualComparison_locallyFinite χ hG A K hK g P d dg Q T hT
  have hSfin := actualComparison_locallyFinite χg hG Ag K hK g⁻¹ Q dg db
    (inverseTargetAt χ K g P) S hS
  have hSfin' := isLocallyFiniteFamily_chartValue_reindex
    (unitaryChart χg hG Ag K hK Q)
    (fun w => unitaryChart χgi hG Agi K hK (inverseTargetAt χ K g P) (zgi w))
    (fun w => (S w).toLinearMap) hSfin zg (zg).continuous
  have hcoef (w : unitaryUnramifiedCharacters (normCharacters χ)) (x : fiber χ A K P w) :
      coefficientMap χ hG A d K hK P w (inverseReturn χ hG A K hK g P w (S (zg w) (T w x))) =
        coefficientMap χ hG A d K hK P w x :=
    (inverseReturn_coefficientMap χ hG A K hK g d db P w _).trans
      ((actualComparison_coefficientMap χg hG Ag K hK g⁻¹ Q dg db (inverseTargetAt χ K g P)
        S hS (zg w) (T w x)).trans (actualComparison_coefficientMap χ hG A K hK g P d dg Q T hT w x))
  have hinj (w : unitaryUnramifiedCharacters (normCharacters χ))
      (hw : w ∈ {w | Function.Injective (coefficientMap χ hG A d K hK P w)}) :
      Function.Injective (coefficientMap χ hG A d K hK P w) := hw
  with_reducible_and_instances
    exact eq_of_chain (unitaryChart χ hG A K hK P)
      (fun w => unitaryChart χg hG Ag K hK Q (zg w))
      (fun w => unitaryChart χgi hG Agi K hK (inverseTargetAt χ K g P) (zgi (zg w)))
      (unitaryChart χ hG A K hK P)
      (fun w => coefficientMap χ hG A d K hK P w) (fun w => coefficientMap χ hG A d K hK P w)
      (fun w => (T w).toLinearMap) (fun w => (S (zg w)).toLinearMap)
      (fun w => (inverseReturn χ hG A K hK g P w).toLinearMap) (fun _ => LinearMap.id)
      hcoef (fun _ _ => rfl) (fun _ => Function.surjective_id)
      (coefficientMap_injective_dense χ hG A K hK d P) hinj
      hTfin hSfin' (inverseReturn_chartValue_const χ hG A K hK g P)
      (isWeaklyContinuousFamily_chartValue_id (unitaryChart χ hG A K hK P)) z v

/-- Both inverse equations with the return transport, using bijectivity of the
  forward comparison. -/
private theorem inverse_at (d : LeviNormalization χ A)
    (dg : LeviNormalization χg Ag) (db : LeviNormalization χgi Agi)
    (P : ParabolicPresentation χ K) (Q : ParabolicPresentation χg K)
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ gG A K K P Q)
    (S : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χg gi Ag K K Q
      (inverseTargetAt χ K g P))
    (hT : IsActualComparison χ hG A K hK g d dg P Q (by with_reducible_and_instances exact T))
    (hS : IsActualComparison χg hG Ag K hK g⁻¹ dg db Q (inverseTargetAt χ K g P)
      (by with_reducible_and_instances exact S))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    TransportedInverse (inverseReturn χ hG A K hK g P z) (S (zg z)) (T z) := by
  exact transportedInverse_of_surjective _ _ _ (actualComparison_bijective χ hG A K hK g P
    d dg Q T hT z).2 (fun v => (transportedValue_iff _ _ _).mpr
      (inverse_loop χ hG A K hK g d dg db P Q T S hT hS z v))

/-- The actual comparison at `g⁻¹` is inverse to the actual comparison at `g`
  after the canonical return transport. -/
theorem inverseLaw (d : LeviNormalization χ A) : InverseLaw χ hG A K hK d := by
  intro g dg db P Q T S z
  with_reducible_and_instances
    exact inverse_at χ hG A K hK g d dg db P Q T.val S.val T.property S.property z

end Inverse

end Langlands.Plancherel.ActualConjugateLeviCoherence
