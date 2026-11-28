import Langlands.Representation.Plancherel.ActualConjugateLeviChartConstancy
import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceAssembly

/-! # The identity law for the actual translated comparison -/

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

section Dense

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (d : LeviNormalization χ A)

/-- The published coefficient map is injective on a dense set of unitary
parameters, by dense unitary irreducibility of the actual normalized
inductions. -/
theorem coefficientMap_injective_dense (P : ParabolicPresentation χ K) :
    Dense {z : unitaryUnramifiedCharacters (normCharacters χ) |
      Function.Injective (coefficientMap χ hG A d K hK P z)} :=
  dense_injective_of_denseUnitaryIrreducibility χ hG A d.center d.central d.quotientMeasure
    d.squareIntegrable d.irreducible K hK
    (ActualCommonLeviV3.denseUnitaryIrreducibility χ A d.center d.central d.quotientMeasure)
    d.splitCenter P

end Dense

section Identity

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts))

set_option hygiene false in
local notation "one" => ((1 : K) : Gpts)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χ₁" => (χ ≫ (G.innerIso one).hom)
set_option hygiene false in
local notation "A₁" => conjugateRepresentation χ one A
set_option hygiene false in
local notation "z₁" => ActualConjugateLeviV3.unitaryConjugateParameter χ one
set_option hygiene false in
local notation "hKK₁" => RationalDynamicSource.conjugateCompact_eq_self one K (1 : K).property

/-- The identity-arrow target presentation, over the anchor conjugated by the
identity point of the compact subgroup. -/
abbrev identityTargetAt (P : ParabolicPresentation χ K) : ParabolicPresentation χ₁ K :=
  identityTarget χ P

/-- The identity-arrow transport, written with the identity point of the
compact subgroup. -/
abbrev identityReturn (P : ParabolicPresentation χ K)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χ₁ A₁ K (identityTargetAt χ K P) (z₁ z)).representation.Equiv
      (fiber χ A K P z).representation := by
  with_reducible_and_instances exact identityTransport χ hG A K hK P z

/-- The identity-arrow transport has a parameter-independent value in the
fixed compact charts. -/
theorem identityReturn_chartValue_const (P : ParabolicPresentation χ K)
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χ₁ hG K hK (identityTargetAt χ K P).cocharacter
          (identityTargetAt χ K P).centralizer_eq (identityTargetAt χ K P).iwasawa A₁
          (ActualCommonLeviV3.unitaryParameter χ₁ (z₁ z)))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (identityReturn χ hG A K hK P z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χ₁ hG K hK (identityTargetAt χ K P).cocharacter
          (identityTargetAt χ K P).centralizer_eq (identityTargetAt χ K P).iwasawa A₁
          (ActualCommonLeviV3.unitaryParameter χ₁ (z₁ z)))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (identityReturn χ hG A K hK P z).toLinearMap) z' := by
  with_reducible_and_instances
    exact identityTransport_chartValue_const χ hG A K hK P z z'

/-- The identity-arrow transport preserves the published coefficient maps. -/
theorem identityReturn_coefficientMap (d : LeviNormalization χ A)
    (d₁ : LeviNormalization χ₁ A₁) (P : ParabolicPresentation χ K)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (y : fiber χ₁ A₁ K (identityTargetAt χ K P) (z₁ z)) :
    coefficientMap χ hG A d K hK P z (identityReturn χ hG A K hK P z y) =
      coefficientMap χ₁ hG A₁ d₁ K hK (identityTargetAt χ K P) (z₁ z) y := by
  with_reducible_and_instances
    exact anchorChange_coefficientMap (conjugationAnchor_one χ).symm hG hK P A
      (conjugateRepresentation χ (1 : Gpts) A) d d₁ z
      (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z)
      (identityTransport χ hG A K hK P z) (identityInducingEquiv χ A z)
      (identityTransport_eq χ hG A K hK P z) y

set_option hygiene false in
local notation "P₁" => conjugatePresentation χ one K K hKK₁ P

set_option maxHeartbeats 1600000 in
/-- The identity loop: for a continuation `U` from the conjugate presentation to
the identity-arrow target which is locally finite in the compact charts, and
such that the translated family preserves the coefficient maps, the
identity-arrow transport undoes the translated family. -/
theorem identity_loop (d : LeviNormalization χ A) (d₁ : LeviNormalization χ₁ A₁)
    (P : ParabolicPresentation χ K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χ₁ A₁ (P₁).cocharacter (P₁).centralizer_eq
      (identityTargetAt χ K P).cocharacter (identityTargetAt χ K P).centralizer_eq)
    (hLF : IsLocallyFiniteFamily (pairValue χ₁ hG A₁ K hK (P₁) (identityTargetAt χ K P) U))
    (hcoef : ∀ (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z),
      coefficientMap χ₁ hG A₁ d₁ K hK (identityTargetAt χ K P) (z₁ z)
          (U (z₁ z) (unitaryTranslation χ one A K K hKK₁ P hG hK hK z v)) =
        coefficientMap χ hG A d K hK P z v)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    identityReturn χ hG A K hK P z
        (U (z₁ z) (unitaryTranslation χ one A K K hKK₁ P hG hK hK z v)) = v :=
  eq_self_of_loop
    (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
      (ActualCommonLeviV3.unitaryParameter χ z))
    (fun z => compactTensorEquiv χ₁ hG K hK (P₁).cocharacter (P₁).centralizer_eq (P₁).iwasawa
      A₁ (ActualCommonLeviV3.unitaryParameter χ₁ (z₁ z)))
    (fun z => compactTensorEquiv χ₁ hG K hK (identityTargetAt χ K P).cocharacter
      (identityTargetAt χ K P).centralizer_eq (identityTargetAt χ K P).iwasawa A₁
      (ActualCommonLeviV3.unitaryParameter χ₁ (z₁ z)))
    (fun z => coefficientMap χ hG A d K hK P z)
    (fun z => (unitaryTranslation χ one A K K hKK₁ P hG hK hK z).toLinearMap)
    (fun z => (U (z₁ z)).toLinearMap)
    (fun z => (identityReturn χ hG A K hK P z).toLinearMap)
    (fun z v => (identityReturn_coefficientMap χ hG A K hK d d₁ P z _).trans (hcoef z v))
    (coefficientMap_injective_dense χ hG A K hK d P) (fun _ hz => hz)
    (unitaryTranslation_chartValue_const χ hG A K hK 1 P)
    (IsLocallyFiniteFamily.comp_continuous hLF
      (ActualConjugateLeviV3.unitaryConjugateParameter χ one).continuous)
    (identityReturn_chartValue_const χ hG A K hK P) z v

set_option maxHeartbeats 1600000 in
/-- The identity law: the actual comparison at the identity point of `K`,
followed by the canonical identification of its target with the original
fiber, is the identity. -/
theorem identityLaw (d : LeviNormalization χ A) : IdentityLaw χ hG A K hK d := by
  intro d₁ P T z v
  have hEx := T.2.2.2
  have hU := hEx.choose_spec.1
  have hTU := hEx.choose_spec.2.1
  have hPCF := hEx.choose_spec.2.2
  have hreg := hU.choose_spec.choose_spec.2.2.2.1
  have hTeq : T.val = (by with_reducible_and_instances
      exact ofCommonLevi χ one A K K hKK₁ P hG hK hK (identityTarget χ P) hEx.choose) := by
    with_reducible exact eq_of_heq hTU
  have hLF := isLocallyFinite_of_regularUnitaryExtension _ hG _ K hK _ _ _ _ hEx.choose hreg
  have hcoef : ∀ (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z),
      coefficientMap χ₁ hG A₁ (by with_reducible_and_instances exact d₁) K hK
          (identityTargetAt χ K P) (z₁ z)
          ((by with_reducible_and_instances exact hEx.choose :
            ActualCommonLeviV3.UnitaryComparisonFamily χ₁ A₁ (P₁).cocharacter
              (P₁).centralizer_eq (identityTargetAt χ K P).cocharacter
              (identityTargetAt χ K P).centralizer_eq) (z₁ z)
            (unitaryTranslation χ one A K K hKK₁ P hG hK hK z v)) =
        coefficientMap χ hG A d K hK P z v := by
    intro z v
    have h2 := (hPCF z).2.1 v
    rw [hTeq] at h2
    simp only [ofCommonLevi, Representation.IntertwiningMap.comp_apply,
      Representation.Equiv.coe_toIntertwiningMap] at h2
    with_reducible_and_instances exact h2
  have hloop := by
    with_reducible_and_instances
      exact identity_loop χ hG A K hK d d₁ P hEx.choose hLF hcoef z v
  have h3 := by
    with_reducible_and_instances
      exact DFunLike.congr_fun (congrFun hTeq z) v
  have happ := by
    with_reducible_and_instances
      exact ofCommonLevi_apply χ hG A K hK 1 P (identityTarget χ P) hEx.choose z v
  unfold TransportedValue
  exact ⟨by with_reducible_and_instances
      exact hEx.choose (z₁ z) (unitaryTranslation χ one A K K hKK₁ P hG hK hK z v),
    by with_reducible_and_instances exact ((heq_of_eq h3).trans (heq_of_eq happ)).symm,
    by with_reducible_and_instances exact heq_of_eq hloop⟩

end Identity

end Langlands.Plancherel.ActualConjugateLeviCoherence
