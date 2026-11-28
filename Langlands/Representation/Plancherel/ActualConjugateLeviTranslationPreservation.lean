import Langlands.Representation.Plancherel.FormalDegreePullbackProof
import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceProof
import Langlands.Representation.Plancherel.TranslatedCompactCoefficientIntegral
import Langlands.Representation.Plancherel.TranslatedCompactProductForm

/-! # Coefficients and forms under the actual unitary translation -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV uG uH

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviCoherence

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact ActualCommonLeviTensor
open ActualCommonLeviCoherence
open ActualConjugateLeviTwist ActualConjugateLeviFiberTransport
open ActualParabolicTranslation ActualParabolicUnitaryTranslation
open Langlands.HarishChandraSchwartz

/-- The pullback formal-degree identity for bundled smooth pullbacks. -/
theorem representationFormalDegree_smoothPullback
    {M : Type uG} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    {N : Type uG} [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    (e : N ≃ₜ* M) (X : SmoothRep.{0, uG, uV} ℂ M)
    (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
    (C' : Subgroup N) [C'.Normal] (hC' : C' ≤ Subgroup.center N)
    (hCC' : C'.map e.toMulEquiv.toMonoidHom = C)
    [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
    [MeasurableSpace (N ⧸ C')] [BorelSpace (N ⧸ C')]
    (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
    (μN : Measure (N ⧸ C')) [μN.IsHaarMeasure] [μN.IsInvInvariant]
    (hμ : μN.map (quotientContinuousMulEquiv e C C' hCC') = μM)
    (hcofM : CompactOpenCofinal M) (hcofN : CompactOpenCofinal N)
    (hρ : IsSquareIntegrableModCentralSubgroup C hC X.representation μM)
    (hiρ : X.representation.IsIrreducible)
    (hσ : IsSquareIntegrableModCentralSubgroup C' hC' (SmoothRep.pullback e X).representation μN)
    (hiσ : (SmoothRep.pullback e X).representation.IsIrreducible) :
    representationFormalDegree C hC μM hcofM hρ hiρ =
      representationFormalDegree C' hC' μN hcofN hσ hiσ :=
  Langlands.Plancherel.representationFormalDegree_pullback e C hC C' hC' hCC' μM μN hμ hcofM hcofN hρ hiρ hσ hiσ

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
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.parabolicLocallyCompact ActualCommonLeviV3.radicalLocallyCompact
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion
  leviLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Cochar" => (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
set_option hygiene false in
local notation "Gpts" => RationalPoint F G.X

section Translation

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (g : K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso (g : Gpts)).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ (g : Gpts) A
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ (g : Gpts)
set_option hygiene false in
local notation "hKK" => RationalDynamicSource.conjugateCompact_eq_self (g : Gpts) K g.property

variable (P : ParabolicPresentation χ K)

set_option hygiene false in
local notation "Pg" => conjugatePresentation χ (g : Gpts) K K hKK P

set_option hygiene false in
local notation "Lg" u => CoefficientConjugation.leviCoefficientLeftTranslation
  (commonDecomposition χ P.cocharacter P.centralizer_eq)
  (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq) (g : Gpts)
  (DynamicCoefficientConjugation.parabolic_mem_conjugation P.cocharacter (g : Gpts))
  (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts))
  (DynamicCoefficientConjugation.radical_mem_conjugation P.cocharacter (g : Gpts))
  (radical_isClosed P.cocharacter) (radical_isClosed (Pg).cocharacter)
  (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG)
  (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG)
  (twistObject χ u A)
set_option hygiene false in
local notation "Ce" e => ActualConjugateLeviTensor.coefficientCongr
  (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq)
  (radical_isClosed (Pg).cocharacter)
  (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG) e
set_option hygiene false in
local notation "hcof₀" => compactOpenCofinal_of_nonarchimedean (levi χ)
set_option hygiene false in
local notation "hcof₁" => compactOpenCofinal_of_nonarchimedean (levi χg)

set_option maxHeartbeats 1200000 in
/-- The compact probability coefficient of a section after the actual product
left translation and any inducing equivalence onto a twist of the conjugate. -/
theorem leviCoefficientMap_translated
    (u : unramifiedCharacters (normCharacters χ))
    (w : unramifiedCharacters (normCharacters χg))
    (e : (conjugateRepresentation χ (g : Gpts) (twistObject χ u A)).representation.Equiv
      (twistObject χg w Ag).representation)
    (hadm : (twistObject χ u A).IsAdmissible)
    (hadm' : (twistObject χg w Ag).IsAdmissible)
    (v : coefficientFiber χ P.cocharacter P.centralizer_eq A u) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
    CompactInduction.leviCoefficientMap
        (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq)
        (radical_isClosed (Pg).cocharacter) (twistObject χg w Ag) K
        (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG) hK
        (DynamicOppositeCanonicalScalar.parabolic_isClosed (Pg).cocharacter)
        (commonProjection_continuous χg (Pg).cocharacter (Pg).centralizer_eq)
        (ActualCommonLeviV3.iwasawa_sets K (Pg).cocharacter (Pg).iwasawa)
        (ActualCommonLeviV3.ambient_modularCharacter hG)
        (ActualCommonLeviV3.common_modularCharacter χg hG (Pg).cocharacter (Pg).centralizer_eq)
        hadm' ((Ce e) ((Lg u) v)) =
      CompactInduction.leviCoefficientMap
        (commonDecomposition χ P.cocharacter P.centralizer_eq)
        (radical_isClosed P.cocharacter) (twistObject χ u A) K
        (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG) hK
        (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter)
        (commonProjection_continuous χ P.cocharacter P.centralizer_eq)
        (ActualCommonLeviV3.iwasawa_sets K P.cocharacter P.iwasawa)
        (ActualCommonLeviV3.ambient_modularCharacter hG)
        (ActualCommonLeviV3.common_modularCharacter χ hG P.cocharacter P.centralizer_eq)
        hadm v := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
  ext x
  rw [CompactInduction.leviCoefficientMap_integral, CompactInduction.leviCoefficientMap_integral]
  exact TranslatedCoefficientValue.integral_leviIntegrand_translated
    (commonDecomposition χ P.cocharacter P.centralizer_eq)
    (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq) K hK g
    (DynamicCoefficientConjugation.parabolic_mem_conjugation P.cocharacter (g : Gpts))
    (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts))
    (DynamicCoefficientConjugation.radical_mem_conjugation P.cocharacter (g : Gpts))
    (radical_isClosed P.cocharacter) (radical_isClosed (Pg).cocharacter)
    (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG)
    (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG)
    (twistObject χ u A) (twistObject χg w Ag) e v x

/-- Formal degrees of an inducing representation and of its actual
conjugate agree for compatible split-central quotient Haar measures. -/
theorem representationFormalDegree_conjugate
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (hc : CompatibleHaar χ A K g d dg) (X : SmoothRep.{0, u, uV} ℂ (levi χ))
    (hsq : IsSquareIntegrableModCentralSubgroup d.center d.central
      X.representation d.quotientMeasure)
    (hi : X.representation.IsIrreducible)
    (hsq' : IsSquareIntegrableModCentralSubgroup dg.center dg.central
      (conjugateRepresentation χ (g : Gpts) X).representation dg.quotientMeasure)
    (hi' : (conjugateRepresentation χ (g : Gpts) X).representation.IsIrreducible) :
    representationFormalDegree dg.center dg.central dg.quotientMeasure hcof₁ hsq' hi' =
      representationFormalDegree d.center d.central d.quotientMeasure hcof₀ hsq hi := by
  obtain ⟨hC, hμ⟩ := hc
  exact (representationFormalDegree_smoothPullback (leviConjugation χ (g : Gpts)).symm X
    d.center d.central dg.center dg.central hC d.quotientMeasure dg.quotientMeasure hμ
    hcof₀ hcof₁ hsq hi hsq' hi').symm

/-- Formal degrees of an inducing twist and of a representation equivalent to
its conjugate agree for compatible split-central quotient Haar measures. -/
theorem representationFormalDegree_conjugate_equiv
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (hc : CompatibleHaar χ A K g d dg) (u : unramifiedCharacters (normCharacters χ))
    (w : unramifiedCharacters (normCharacters χg))
    (e : (conjugateRepresentation χ (g : Gpts) (twistObject χ u A)).representation.Equiv
      (twistObject χg w Ag).representation)
    (hsq : IsSquareIntegrableModCentralSubgroup d.center d.central
      (twistObject χ u A).representation d.quotientMeasure)
    (hi : (twistObject χ u A).representation.IsIrreducible)
    (hsq' : IsSquareIntegrableModCentralSubgroup dg.center dg.central
      (twistObject χg w Ag).representation dg.quotientMeasure)
    (hi' : (twistObject χg w Ag).representation.IsIrreducible) :
    representationFormalDegree dg.center dg.central dg.quotientMeasure hcof₁ hsq' hi' =
      representationFormalDegree d.center d.central d.quotientMeasure hcof₀ hsq hi := by
  have hc' := hc
  obtain ⟨hC, hμ⟩ := hc'
  have hsqc := ActualConjugateLeviV3.conjugate_squareIntegrable χ (g : Gpts) (twistObject χ u A)
    d.center d.central dg.center dg.central hC d.quotientMeasure dg.quotientMeasure hμ hsq
  have hic := ActualConjugateLeviV3.conjugate_irreducible χ (g : Gpts) (twistObject χ u A) hi
  exact (representationFormalDegree_equiv dg.center dg.central dg.quotientMeasure hcof₁
      e hsqc hic hsq' hi').trans
    (representationFormalDegree_conjugate χ A K g d dg hc (twistObject χ u A) hsq hi hsqc hic)

set_option maxHeartbeats 1600000 in
/-- The inverse-formal-degree product form after the actual product left
translation and any inducing equivalence onto a twist of the conjugate, for
compatible split-central quotient Haar measures. -/
theorem leviFormalDegreeProductForm_translated
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (hc : CompatibleHaar χ A K g d dg) (u : unramifiedCharacters (normCharacters χ))
    (w : unramifiedCharacters (normCharacters χg))
    (e : (conjugateRepresentation χ (g : Gpts) (twistObject χ u A)).representation.Equiv
      (twistObject χg w Ag).representation)
    (hsq : IsSquareIntegrableModCentralSubgroup d.center d.central
      (twistObject χ u A).representation d.quotientMeasure)
    (hi : (twistObject χ u A).representation.IsIrreducible)
    (hsq' : IsSquareIntegrableModCentralSubgroup dg.center dg.central
      (twistObject χg w Ag).representation dg.quotientMeasure)
    (hi' : (twistObject χg w Ag).representation.IsIrreducible)
    (v v' : coefficientFiber χ P.cocharacter P.centralizer_eq A u) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
    (CompactInduction.leviFormalDegreeProductForm
        (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq)
        (radical_isClosed (Pg).cocharacter) (twistObject χg w Ag) K
        (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG) hK
        (DynamicOppositeCanonicalScalar.parabolic_isClosed (Pg).cocharacter)
        (ActualCommonLeviV3.iwasawa_sets K (Pg).cocharacter (Pg).iwasawa)
        (ActualCommonLeviV3.ambient_modularCharacter hG)
        (ActualCommonLeviV3.common_modularCharacter χg hG (Pg).cocharacter (Pg).centralizer_eq)
        hcof₁ dg.center dg.central dg.quotientMeasure hsq' hi').inner
        ((Ce e) ((Lg u) v)) ((Ce e) ((Lg u) v')) =
      (CompactInduction.leviFormalDegreeProductForm
        (commonDecomposition χ P.cocharacter P.centralizer_eq)
        (radical_isClosed P.cocharacter) (twistObject χ u A) K
        (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG) hK
        (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter)
        (ActualCommonLeviV3.iwasawa_sets K P.cocharacter P.iwasawa)
        (ActualCommonLeviV3.ambient_modularCharacter hG)
        (ActualCommonLeviV3.common_modularCharacter χ hG P.cocharacter P.centralizer_eq)
        hcof₀ d.center d.central d.quotientMeasure hsq hi).inner v v' := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
  let b := Classical.choice (isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    d.center d.central d.quotientMeasure hcof₀ hsq)
  let c := Classical.choice (isUnitarizable_of_isSquareIntegrableModCentralSubgroup
    dg.center dg.central dg.quotientMeasure hcof₁ hsq')
  have e1 := CompactInduction.leviFormalDegreeProductForm_eq
    (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq)
    (radical_isClosed (Pg).cocharacter) (twistObject χg w Ag) K
    (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed (Pg).cocharacter)
    (ActualCommonLeviV3.iwasawa_sets K (Pg).cocharacter (Pg).iwasawa)
    (ActualCommonLeviV3.ambient_modularCharacter hG)
    (ActualCommonLeviV3.common_modularCharacter χg hG (Pg).cocharacter (Pg).centralizer_eq)
    hcof₁ dg.center dg.central dg.quotientMeasure hsq' hi' c
  have e2 := CompactInduction.leviFormalDegreeProductForm_eq
    (commonDecomposition χ P.cocharacter P.centralizer_eq)
    (radical_isClosed P.cocharacter) (twistObject χ u A) K
    (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG) hK
    (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter)
    (ActualCommonLeviV3.iwasawa_sets K P.cocharacter P.iwasawa)
    (ActualCommonLeviV3.ambient_modularCharacter hG)
    (ActualCommonLeviV3.common_modularCharacter χ hG P.cocharacter P.centralizer_eq)
    hcof₀ d.center d.central d.quotientMeasure hsq hi b
  have hform := TranslatedCoefficientValue.leviProductForm_inner_translated_of_irreducible
    (commonDecomposition χ P.cocharacter P.centralizer_eq)
    (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq) K hK g
    (DynamicCoefficientConjugation.parabolic_mem_conjugation P.cocharacter (g : Gpts))
    (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts))
    (DynamicCoefficientConjugation.radical_mem_conjugation P.cocharacter (g : Gpts))
    (radical_isClosed P.cocharacter) (radical_isClosed (Pg).cocharacter)
    (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG)
    (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG)
    (twistObject χ u A) (twistObject χg w Ag) e hsq.1 hsq'.1 hcof₀ hcof₁ b
    (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter)
    (DynamicOppositeCanonicalScalar.parabolic_isClosed (Pg).cocharacter)
    (ActualCommonLeviV3.iwasawa_sets K P.cocharacter P.iwasawa)
    (ActualCommonLeviV3.iwasawa_sets K (Pg).cocharacter (Pg).iwasawa)
    (ActualCommonLeviV3.ambient_modularCharacter hG)
    (ActualCommonLeviV3.common_modularCharacter χ hG P.cocharacter P.centralizer_eq)
    (ActualCommonLeviV3.common_modularCharacter χg hG (Pg).cocharacter (Pg).centralizer_eq)
    hi' c v v'
  have hdeg := representationFormalDegree_conjugate_equiv χ A K g d dg hc u w e hsq hi hsq' hi'
  rw [e1, e2, InvariantPositiveForm.rescale_inner, InvariantPositiveForm.rescale_inner, hdeg]
  exact congrArg (HMul.hMul _) hform

/-- Any equivalence of fibers that is the actual product left translation
followed by the transport along an inducing equivalence preserves the
normalized coefficient map. -/
theorem coefficientMap_of_eq_translated
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (T : (fiber χ A K P z).representation.Equiv (fiber χg Ag K (Pg) (zg z)).representation)
    (E : (conjugateRepresentation χ (g : Gpts)
      (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation.Equiv
      (twistObject χg (ActualCommonLeviV3.unitaryParameter χg (zg z)) Ag).representation)
    (hT : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
      T = (Lg (ActualCommonLeviV3.unitaryParameter χ z)).trans (Ce E))
    (v : fiber χ A K P z) :
    coefficientMap χg hG Ag dg K hK (Pg) (zg z) (T v) =
      coefficientMap χ hG A d K hK P z v := by
  subst hT
  rw [Representation.Equiv.trans_apply]
  delta coefficientMap ActualCommonLeviV3.coefficientMap
  exact leviCoefficientMap_translated χ hG A K hK g P
    (ActualCommonLeviV3.unitaryParameter χ z) (ActualCommonLeviV3.unitaryParameter χg (zg z))
    E _ _ v

/-- Any equivalence of fibers that is the actual product left translation
followed by the transport along an inducing equivalence preserves the
inverse-formal-degree form, for compatible quotient Haar measures. -/
theorem formalDegreeForm_of_eq_translated
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (hc : CompatibleHaar χ A K g d dg)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (T : (fiber χ A K P z).representation.Equiv (fiber χg Ag K (Pg) (zg z)).representation)
    (E : (conjugateRepresentation χ (g : Gpts)
      (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation.Equiv
      (twistObject χg (ActualCommonLeviV3.unitaryParameter χg (zg z)) Ag).representation)
    (hT : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
      T = (Lg (ActualCommonLeviV3.unitaryParameter χ z)).trans (Ce E))
    (v v' : fiber χ A K P z) :
    (formalDegreeForm χg hG Ag dg K hK (Pg) (zg z)).inner (T v) (T v') =
      (formalDegreeForm χ hG A d K hK P z).inner v v' := by
  subst hT
  simp only [Representation.Equiv.trans_apply]
  delta formalDegreeForm ActualCommonLeviV3.formalDegreeForm
  exact leviFormalDegreeProductForm_translated χ hG A K hK g P d dg hc
    (ActualCommonLeviV3.unitaryParameter χ z) (ActualCommonLeviV3.unitaryParameter χg (zg z))
    E _ _ _ _ v v'

end Translation

end Langlands.Plancherel.ActualConjugateLeviCoherence
