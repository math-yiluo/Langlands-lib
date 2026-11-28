import Langlands.Representation.Plancherel.ActualConjugateLeviChartConstancy

/-! # Local finiteness of actual translated comparisons in compact charts -/

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

section Reindexing

/-- Reading a reindexed family in the reindexed charts preserves local finiteness. -/
theorem isLocallyFiniteFamily_chartValue_reindex
    {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']
    {S T : Z' → Type*} [∀ z, AddCommGroup (S z)] [∀ z, Module ℂ (S z)]
    [∀ z, AddCommGroup (T z)] [∀ z, Module ℂ (T z)]
    {V₀ V₁ : Type*} [AddCommGroup V₀] [Module ℂ V₀] [AddCommGroup V₁] [Module ℂ V₁]
    (cS : ∀ z, S z ≃ₗ[ℂ] V₀) (cT : ∀ z, T z ≃ₗ[ℂ] V₁)
    (Φ : ∀ z, S z →ₗ[ℂ] T z) (h : IsLocallyFiniteFamily (chartValue cS cT Φ))
    (φ : Z → Z') (hφ : Continuous φ) :
    IsLocallyFiniteFamily
      (chartValue (fun z => cS (φ z)) (fun z => cT (φ z)) (fun z => Φ (φ z))) :=
  IsLocallyFiniteFamily.comp_continuous h hφ

end Reindexing

section Comparison

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts))

/-- The compact tensor chart of a unitary fiber at a parabolic presentation. -/
abbrev unitaryChart (P : ParabolicPresentation χ K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :=
  compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
    (ActualCommonLeviV3.unitaryParameter χ z)

variable (g : K) (P : ParabolicPresentation χ K)

set_option hygiene false in
local notation "gG" => (g : Gpts)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso gG).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ gG A
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ gG
set_option hygiene false in
local notation "hKK" => RationalDynamicSource.conjugateCompact_eq_self gG K g.property
set_option hygiene false in
local notation "Pg" => conjugatePresentation χ gG K K hKK P

/-- A translated comparison built from a locally finite common-Levi extension
is locally finite in the compact charts of its source and target. -/
theorem ofCommonLevi_locallyFinite (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag (Pg).cocharacter (Pg).centralizer_eq
      Q.cocharacter Q.centralizer_eq)
    (hU : IsLocallyFiniteFamily (pairValue χg hG Ag K hK (Pg) Q U)) :
    IsLocallyFiniteFamily (chartValue (unitaryChart χ hG A K hK P)
      (fun z => unitaryChart χg hG Ag K hK Q (zg z))
      (fun z => (ofCommonLevi χ gG A K K hKK P hG hK hK Q U z).toLinearMap)) := by
  simp only [ofCommonLevi, Representation.IntertwiningMap.comp_toLinearMap]
  have hU' := isLocallyFiniteFamily_chartValue_reindex (unitaryChart χg hG Ag K hK (Pg))
    (unitaryChart χg hG Ag K hK Q) (fun z => (U z).toLinearMap) hU zg (zg).continuous
  have hcomp := isLocallyFiniteFamily_chartValue_comp₂
    (unitaryChart χ hG A K hK P)
    (fun z => unitaryChart χg hG Ag K hK (Pg) (zg z))
    (fun z => unitaryChart χg hG Ag K hK Q (zg z))
    (fun z => (unitaryTranslation χ gG A K K hKK P hG hK hK z).toLinearMap)
    (fun z => (U (zg z)).toLinearMap)
    (unitaryTranslation_chartValue_const χ hG A K hK g P) hU'
  with_reducible_and_instances exact hcomp

set_option maxHeartbeats 1600000 in
/-- The continuation certificate of an actual comparison gives local finiteness
of its values in the compact charts. -/
theorem actualComparison_locallyFinite (d : LeviNormalization χ A)
    (dg : LeviNormalization χg Ag) (Q : ParabolicPresentation χg K)
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ gG A K K P Q)
    (hT : IsActualComparison χ hG A K hK g d dg P Q (by with_reducible_and_instances exact T)) :
    IsLocallyFiniteFamily (chartValue (unitaryChart χ hG A K hK P)
      (fun z => unitaryChart χg hG Ag K hK Q (zg z)) (fun z => (T z).toLinearMap)) := by
  have hEx := hT.2.2
  have hreg := hEx.choose_spec.1.choose_spec.choose_spec.2.2.2.1
  have hLF := isLocallyFinite_of_regularUnitaryExtension _ hG _ K hK _ _ _ _ hEx.choose hreg
  have hEq : T = ofCommonLevi χ gG A K K hKK P hG hK hK Q
      (by with_reducible_and_instances exact hEx.choose) := by
    with_reducible_and_instances exact eq_of_heq hEx.choose_spec.2.1
  rw [hEq]
  with_reducible_and_instances
    exact ofCommonLevi_locallyFinite χ hG A K hK g P Q hEx.choose hLF

/-- The coefficient identity on the fibers of the translated comparison. -/
theorem actualComparison_coefficientMap (d : LeviNormalization χ A)
    (dg : LeviNormalization χg Ag) (Q : ParabolicPresentation χg K)
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ gG A K K P Q)
    (hT : IsActualComparison χ hG A K hK g d dg P Q (by with_reducible_and_instances exact T))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    coefficientMap χg hG Ag dg K hK Q (zg z) (T z v) =
      coefficientMap χ hG A d K hK P z v := by
  have hc := (hT.2.2.choose_spec.2.2 z).2.1 v
  with_reducible_and_instances exact hc

/-- The certificate of an actual translated comparison gives pointwise bijectivity. -/
theorem actualComparison_bijective (d : LeviNormalization χ A)
    (dg : LeviNormalization χg Ag) (Q : ParabolicPresentation χg K)
    (T : ActualParabolicUnitaryTranslation.UnitaryComparisonFamily χ gG A K K P Q)
    (hT : IsActualComparison χ hG A K hK g d dg P Q (by with_reducible_and_instances exact T))
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    Function.Bijective (T z) := by
  have hb := (hT.2.2.choose_spec.2.2 z).1
  with_reducible_and_instances exact hb

end Comparison

end Langlands.Plancherel.ActualConjugateLeviCoherence
