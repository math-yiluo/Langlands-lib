import Langlands.Representation.Plancherel.ActualConjugateLeviExistence
import Langlands.Representation.Plancherel.ActualConjugateLeviCompactChartFramework
import Langlands.Representation.Plancherel.TranslatedCoefficientInverse

/-! # The translation and the fiber transports in fixed compact charts -/

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

/-- After removal of the twists, the actual product left translation followed
by an inducing equivalence with identity vector map reads the source values at
the left translate, through the fixed coefficient-value conjugation. -/
theorem translated_untwist_eval (z : unitaryUnramifiedCharacters (normCharacters χ))
    (T : (fiber χ A K P z).representation.Equiv (fiber χg Ag K (Pg) (zg z)).representation)
    (E : (conjugateRepresentation χ (g : Gpts)
      (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation.Equiv
      (twistObject χg (ActualCommonLeviV3.unitaryParameter χg (zg z)) Ag).representation)
    (hE : HEq E.toLinearEquiv (LinearEquiv.refl ℂ A))
    (hT : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
      T = (Lg (ActualCommonLeviV3.unitaryParameter χ z)).trans (Ce E))
    (f : fiber χ A K P z) (k : RationalPoint F G.X × RationalPoint F G.X) :
    untwistValue χg Ag (ActualCommonLeviV3.unitaryParameter χg (zg z))
        (fiberEval χg (Pg).cocharacter (Pg).centralizer_eq Ag
          (ActualCommonLeviV3.unitaryParameter χg (zg z)) (T f) k) =
      TranslatedCoefficientValue.conjugateValue (g : Gpts)
        (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts)) A
        (untwistValue χ A (ActualCommonLeviV3.unitaryParameter χ z)
          (fiberEval χ P.cocharacter P.centralizer_eq A
            (ActualCommonLeviV3.unitaryParameter χ z) f (((g : Gpts), (g : Gpts))⁻¹ * k))) := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
  subst hT
  exact TranslatedCoefficientValue.untwist_translated_eval
    (commonDecomposition χ P.cocharacter P.centralizer_eq)
    (commonDecomposition χg (Pg).cocharacter (Pg).centralizer_eq) (g : Gpts)
    (DynamicCoefficientConjugation.parabolic_mem_conjugation P.cocharacter (g : Gpts))
    (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts))
    (DynamicCoefficientConjugation.radical_mem_conjugation P.cocharacter (g : Gpts))
    (radical_isClosed P.cocharacter) (radical_isClosed (Pg).cocharacter)
    (DynamicOppositeCanonicalScalar.radical_unimodular P.cocharacter hG)
    (DynamicOppositeCanonicalScalar.radical_unimodular (Pg).cocharacter hG)
    (leviNormCharacters χ) (leviNormCharacters χg) A
    (parameterTransport χ (ActualCommonLeviV3.unitaryParameter χ z))
    (parameterTransport χg (ActualCommonLeviV3.unitaryParameter χg (zg z))) E hE f k

/-- The unitary translation has a parameter-independent value in the fixed
compact charts. -/
theorem unitaryTranslation_chartValue_const
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => compactTensorEquiv χg hG K hK (Pg).cocharacter (Pg).centralizer_eq
          (Pg).iwasawa Ag (ActualCommonLeviV3.unitaryParameter χg (zg z)))
        (fun z => (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => compactTensorEquiv χg hG K hK (Pg).cocharacter (Pg).centralizer_eq
          (Pg).iwasawa Ag (ActualCommonLeviV3.unitaryParameter χg (zg z)))
        (fun z => (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z).toLinearMap) z' :=
  compactValue_const_of_eval hG K hK χ P.cocharacter P.centralizer_eq P.iwasawa A
    χg (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa Ag
    (ActualCommonLeviV3.unitaryParameter χ)
    (fun z => ActualCommonLeviV3.unitaryParameter χg (zg z))
    (fun z => (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z).toLinearMap)
    (g : Gpts) g.property
    (TranslatedCoefficientValue.conjugateValue (g : Gpts)
      (DynamicCoefficientConjugation.levi_mem_conjugation χ (g : Gpts)) A)
    (fun z f k => translated_untwist_eval χ hG A K hK g P z _
      (unitaryTwistEquiv χ (g : Gpts) A z) (unitaryTwistEquiv_linear_heq χ (g : Gpts) A z)
      (unitaryTranslation_eq χ (g : Gpts) A K K hKK P hG hK hK z) f k) z z'

end Translation


section Anchor

variable {χ φ : Cochar} (h : χ = φ) (hG : IsConnectedReductive G)
  {K : OpenSubgroup Gpts} (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (B : SmoothRep.{0, u, uV} ℂ (levi φ))

set_option hygiene false in
local notation "anchorPullback " h:max =>
  (@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _
    (anchorMembership h))

set_option hygiene false in
local notation "L₁" X => CoefficientConjugation.leviCoefficientLeftTranslation
  (fiberDecomposition P) (fiberDecomposition (changeAnchor h P))
  1 (changeAnchor_parabolicMembership h P) (anchorMembership h)
  (changeAnchor_radicalMembership h P)
  (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
  (radicalUnimodular P.cocharacter hG)
  (radicalUnimodular (changeAnchor h P).cocharacter hG) X

set_option hygiene false in
local notation "C₁" e => ActualConjugateLeviTensor.coefficientCongr
  (fiberDecomposition (changeAnchor h P)) (fiberRadicalClosed (changeAnchor h P))
  (radicalUnimodular (changeAnchor h P).cocharacter hG) e

/-- Suppose the inducing equivalence for the change of Levi anchor has the
underlying linear map of `cmp.symm`. After untwisting, the transported value
at `k` is obtained from the `B` coefficient value at `k` by applying
`productCoefficientLeviEquiv cmp.symm` and then inverse coefficient-value
conjugation at the identity. -/
theorem anchorChange_untwist_eval
    (cmp : ((anchorPullback h).obj A).representation.Equiv B.representation)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (w : unitaryUnramifiedCharacters (normCharacters φ))
    (T : (fiber φ B K (changeAnchor h P) w).representation.Equiv
      (fiber χ A K P z).representation)
    (E : (twistObject φ (ActualCommonLeviV3.unitaryParameter φ w) B).representation.Equiv
      ((anchorPullback h).obj
        (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation)
    (hE : HEq E.toLinearEquiv cmp.symm.toLinearEquiv)
    (hT : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
      T = (by with_reducible_and_instances
        exact (C₁ E).trans (L₁ (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).symm))
    (f : fiber φ B K (changeAnchor h P) w) (k : Gpts × Gpts) :
    untwistValue χ A (ActualCommonLeviV3.unitaryParameter χ z)
        (fiberEval χ P.cocharacter P.centralizer_eq A
          (ActualCommonLeviV3.unitaryParameter χ z) (T f) k) =
      (TranslatedCoefficientValue.conjugateValue (1 : Gpts) (anchorMembership h) A).symm
        (productCoefficientLeviEquiv cmp.symm
          (untwistValue φ B (ActualCommonLeviV3.unitaryParameter φ w)
            (fiberEval φ (changeAnchor h P).cocharacter (changeAnchor h P).centralizer_eq B
              (ActualCommonLeviV3.unitaryParameter φ w) f
              (((1 : Gpts), (1 : Gpts))⁻¹ * k)))) := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
  subst hT
  simp only [Representation.Equiv.trans_apply]
  have key := TranslatedCoefficientValue.untwist_inverseTranslated_eval
    (fiberDecomposition P) (fiberDecomposition (changeAnchor h P))
    1 (changeAnchor_parabolicMembership h P) (anchorMembership h)
    (changeAnchor_radicalMembership h P)
    (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
    (radicalUnimodular P.cocharacter hG)
    (radicalUnimodular (changeAnchor h P).cocharacter hG)
    (leviNormCharacters χ) (leviNormCharacters φ) A
    (parameterTransport χ (ActualCommonLeviV3.unitaryParameter χ z))
    (parameterTransport φ (ActualCommonLeviV3.unitaryParameter φ w)) B cmp E hE
    (by with_reducible_and_instances exact f) k (((1 : Gpts), (1 : Gpts))⁻¹ * k)
    (Prod.ext (by simp) (by simp))
  with_reducible_and_instances
    exact (LinearEquiv.eq_symm_apply _).mpr key

end Anchor

section AnchorCoefficients

attribute [local instance]
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.parabolicLocallyCompact ActualCommonLeviV3.radicalLocallyCompact
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {χ φ : Cochar} (h : χ = φ) (hG : IsConnectedReductive G)
  {K : OpenSubgroup Gpts} (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ)) (B : SmoothRep.{0, u, uV} ℂ (levi φ))

set_option hygiene false in
local notation "anchorPullback " h:max =>
  (@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _
    (anchorMembership h))

set_option hygiene false in
local notation "L₁" X => CoefficientConjugation.leviCoefficientLeftTranslation
  (fiberDecomposition P) (fiberDecomposition (changeAnchor h P))
  1 (changeAnchor_parabolicMembership h P) (anchorMembership h)
  (changeAnchor_radicalMembership h P)
  (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
  (radicalUnimodular P.cocharacter hG)
  (radicalUnimodular (changeAnchor h P).cocharacter hG) X

set_option hygiene false in
local notation "C₁" e => ActualConjugateLeviTensor.coefficientCongr
  (fiberDecomposition (changeAnchor h P)) (fiberRadicalClosed (changeAnchor h P))
  (radicalUnimodular (changeAnchor h P).cocharacter hG) e

set_option maxHeartbeats 1600000 in
/-- A change-of-anchor transport, made of an inducing equivalence followed by
the inverse product left translation by the identity point, preserves the
published coefficient maps. -/
theorem anchorChange_coefficientMap (d : LeviNormalization χ A) (dφ : LeviNormalization φ B)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (w : unitaryUnramifiedCharacters (normCharacters φ))
    (T : (fiber φ B K (changeAnchor h P) w).representation.Equiv
      (fiber χ A K P z).representation)
    (E : (twistObject φ (ActualCommonLeviV3.unitaryParameter φ w) B).representation.Equiv
      ((anchorPullback h).obj
        (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation)
    (hT : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
      T = (by with_reducible_and_instances
        exact (C₁ E).trans (L₁ (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).symm))
    (f : fiber φ B K (changeAnchor h P) w) :
    coefficientMap χ hG A d K hK P z (T f) =
      coefficientMap φ hG B dφ K hK (changeAnchor h P) w f := by
  letI := quotientCompact K hK P.cocharacter P.iwasawa
  letI := quotientCompact K hK (changeAnchor h P).cocharacter (changeAnchor h P).iwasawa
  subst hT
  simp only [Representation.Equiv.trans_apply]
  delta coefficientMap ActualCommonLeviV3.coefficientMap
  have hB : (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A).IsAdmissible :=
    (ActualCommonLeviV3.unitaryTwist_squareIntegrable χ A d.center d.central
      d.quotientMeasure d.squareIntegrable z).1
  have hA : (twistObject φ (ActualCommonLeviV3.unitaryParameter φ w) B).IsAdmissible :=
    (ActualCommonLeviV3.unitaryTwist_squareIntegrable φ B dφ.center dφ.central
      dφ.quotientMeasure dφ.squareIntegrable w).1
  with_reducible_and_instances
    exact TranslatedCoefficientValue.leviCoefficientMap_inverseTranslated_of_mem
      (fiberDecomposition P) (fiberDecomposition (changeAnchor h P)) K hK 1 K.one_mem
      (changeAnchor_parabolicMembership h P) (anchorMembership h)
      (changeAnchor_radicalMembership h P)
      (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor h P))
      (radicalUnimodular P.cocharacter hG)
      (radicalUnimodular (changeAnchor h P).cocharacter hG)
      (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)
      (twistObject φ (ActualCommonLeviV3.unitaryParameter φ w) B) E
      (DynamicOppositeCanonicalScalar.parabolic_isClosed P.cocharacter)
      (DynamicOppositeCanonicalScalar.parabolic_isClosed (changeAnchor h P).cocharacter)
      (commonProjection_continuous χ P.cocharacter P.centralizer_eq)
      (commonProjection_continuous φ (changeAnchor h P).cocharacter
        (changeAnchor h P).centralizer_eq)
      (ActualCommonLeviV3.iwasawa_sets K P.cocharacter P.iwasawa)
      (ActualCommonLeviV3.iwasawa_sets K (changeAnchor h P).cocharacter
        (changeAnchor h P).iwasawa)
      (ActualCommonLeviV3.ambient_modularCharacter hG)
      (ActualCommonLeviV3.common_modularCharacter χ hG P.cocharacter P.centralizer_eq)
      (ActualCommonLeviV3.common_modularCharacter φ hG (changeAnchor h P).cocharacter
        (changeAnchor h P).centralizer_eq)
      hB hA f

end AnchorCoefficients

section IdentityChart

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χone" => (χ ≫ (G.innerIso (1 : Gpts)).hom)
set_option hygiene false in
local notation "hone" => (conjugationAnchor_one χ).symm

/-- The identity-arrow transport between the displayed actual fibers. -/
abbrev identityTransport (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χone (conjugateRepresentation χ (1 : Gpts) A) K (changeAnchor hone P)
      (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z)).representation.Equiv
      (fiber χ A K P z).representation := by
  with_reducible exact identityEquiv χ hG A hK P z

/-- The identity-arrow transport between the displayed fibers is the same-Levi
transport along `identityInducingEquiv` followed by the inverse product left
translation by the identity point. -/
theorem identityTransport_eq (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (changeAnchor hone P).cocharacter
      (changeAnchor hone P).iwasawa
    identityTransport χ hG A K hK P z = (by with_reducible_and_instances
      exact (ActualConjugateLeviTensor.coefficientCongr
          (fiberDecomposition (changeAnchor hone P)) (fiberRadicalClosed (changeAnchor hone P))
          (radicalUnimodular (changeAnchor hone P).cocharacter hG)
          (identityInducingEquiv χ A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition P) (fiberDecomposition (changeAnchor hone P))
          1 (changeAnchor_parabolicMembership hone P) (anchorMembership hone)
          (changeAnchor_radicalMembership hone P)
          (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor hone P))
          (radicalUnimodular P.cocharacter hG)
          (radicalUnimodular (changeAnchor hone P).cocharacter hG)
          (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).symm) := by
  with_reducible_and_instances
    exact identityEquiv_eq χ hG A hK P z

/-- The identity-point comparison of the original Levi representation with
its conjugate by the identity point. -/
def identityComparison :
    ((@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _
      (anchorMembership hone)).obj A).representation.Equiv
      (conjugateRepresentation χ (1 : Gpts) A).representation :=
  TranslatedCoefficientValue.pullbackCongrEquiv _ (leviConjugation χ (1 : Gpts)).symm A
    (fun n => (identity_point_eq χ n).symm)

/-- The identity-arrow transport has a parameter-independent value in the
fixed compact charts. -/
theorem identityTransport_chartValue_const
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χone hG K hK (changeAnchor hone P).cocharacter
          (changeAnchor hone P).centralizer_eq (changeAnchor hone P).iwasawa
          (conjugateRepresentation χ (1 : Gpts) A)
          (ActualCommonLeviV3.unitaryParameter χone
            (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z)))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (identityTransport χ hG A K hK P z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χone hG K hK (changeAnchor hone P).cocharacter
          (changeAnchor hone P).centralizer_eq (changeAnchor hone P).iwasawa
          (conjugateRepresentation χ (1 : Gpts) A)
          (ActualCommonLeviV3.unitaryParameter χone
            (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z)))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (identityTransport χ hG A K hK P z).toLinearMap) z' := by
  have hE : ∀ z : unitaryUnramifiedCharacters (normCharacters χ),
      HEq (identityInducingEquiv χ A z).toLinearEquiv
        (identityComparison χ A).symm.toLinearEquiv := fun z =>
    (identityInducingEquiv_linear_heq χ A z).trans
      (TranslatedCoefficientValue.pullbackCongrEquiv_symm_linear_heq _ _ A _).symm
  have hM := fun (z : unitaryUnramifiedCharacters (normCharacters χ)) f k =>
    anchorChange_untwist_eval hone hG hK P A
      (conjugateRepresentation χ (1 : Gpts) A) (identityComparison χ A) z
      (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z)
      (identityTransport χ hG A K hK P z) (identityInducingEquiv χ A z) (hE z)
      (identityTransport_eq χ hG A K hK P z) f k
  exact compactValue_const_of_eval hG K hK χone (changeAnchor hone P).cocharacter
    (changeAnchor hone P).centralizer_eq (changeAnchor hone P).iwasawa
    (conjugateRepresentation χ (1 : Gpts) A) χ P.cocharacter P.centralizer_eq P.iwasawa A
    (fun z => ActualCommonLeviV3.unitaryParameter χone
      (ActualConjugateLeviV3.unitaryConjugateParameter χ 1 z))
    (ActualCommonLeviV3.unitaryParameter χ)
    (fun z => (identityTransport χ hG A K hK P z).toLinearMap) 1 K.one_mem
    (fun t => (TranslatedCoefficientValue.conjugateValue (1 : Gpts)
      (anchorMembership hone) A).symm
        (productCoefficientLeviEquiv (identityComparison χ A).symm t))
    (fun z f k => hM z f k) z z'

end IdentityChart

section InverseChart

variable (χ : Cochar) (g : Gpts) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (P : ParabolicPresentation χ K)

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χback" => (χg ≫ (G.innerIso g⁻¹).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "Aback" => conjugateRepresentation χg g⁻¹ Ag
set_option hygiene false in
local notation "zg" => ActualConjugateLeviV3.unitaryConjugateParameter χ g
set_option hygiene false in
local notation "zback" => ActualConjugateLeviV3.unitaryConjugateParameter χg g⁻¹
set_option hygiene false in
local notation "hback" => (conjugationAnchor_inv χ g).symm

/-- The inverse-arrow transport between the displayed actual fibers. -/
abbrev inverseTransport (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χback Aback K (changeAnchor hback P) (zback (zg z))).representation.Equiv
      (fiber χ A K P z).representation := by
  with_reducible exact inverseEquiv χ g hG A hK P z

/-- The inverse-arrow transport between the displayed fibers is the same-Levi
transport along `inverseInducingEquiv` followed by the inverse product left
translation by the identity point. -/
theorem inverseTransport_eq (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK P.cocharacter P.iwasawa
    letI := quotientCompact K hK (changeAnchor hback P).cocharacter
      (changeAnchor hback P).iwasawa
    inverseTransport χ g hG A K hK P z = (by with_reducible_and_instances
      exact (ActualConjugateLeviTensor.coefficientCongr
          (fiberDecomposition (changeAnchor hback P)) (fiberRadicalClosed (changeAnchor hback P))
          (radicalUnimodular (changeAnchor hback P).cocharacter hG)
          (inverseInducingEquiv χ g A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition P) (fiberDecomposition (changeAnchor hback P))
          1 (changeAnchor_parabolicMembership hback P) (anchorMembership hback)
          (changeAnchor_radicalMembership hback P)
          (fiberRadicalClosed P) (fiberRadicalClosed (changeAnchor hback P))
          (radicalUnimodular P.cocharacter hG)
          (radicalUnimodular (changeAnchor hback P).cocharacter hG)
          (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).symm) := by
  with_reducible_and_instances
    exact inverseEquiv_eq χ g hG A hK P z

/-- The comparison of the original Levi representation, pulled back along
conjugation by the identity point, with its conjugate by `g` and then by
`g⁻¹`. -/
def inverseComparison :
    ((@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _
      (anchorMembership hback)).obj A).representation.Equiv (Aback).representation :=
  TranslatedCoefficientValue.pullbackPullbackCongrEquiv _ (leviConjugation χ g).symm
    (leviConjugation χg g⁻¹).symm A (fun n => (inverse_point_eq χ g n).symm)

/-- The inverse-arrow transport has a parameter-independent value in the
fixed compact charts. -/
theorem inverseTransport_chartValue_const
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χback hG K hK (changeAnchor hback P).cocharacter
          (changeAnchor hback P).centralizer_eq (changeAnchor hback P).iwasawa Aback
          (ActualCommonLeviV3.unitaryParameter χback (zback (zg z))))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (inverseTransport χ g hG A K hK P z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χback hG K hK (changeAnchor hback P).cocharacter
          (changeAnchor hback P).centralizer_eq (changeAnchor hback P).iwasawa Aback
          (ActualCommonLeviV3.unitaryParameter χback (zback (zg z))))
        (fun z => compactTensorEquiv χ hG K hK P.cocharacter P.centralizer_eq P.iwasawa A
          (ActualCommonLeviV3.unitaryParameter χ z))
        (fun z => (inverseTransport χ g hG A K hK P z).toLinearMap) z' := by
  have hE : ∀ z : unitaryUnramifiedCharacters (normCharacters χ),
      HEq (inverseInducingEquiv χ g A z).toLinearEquiv
        (inverseComparison χ g A).symm.toLinearEquiv := fun z =>
    (inverseInducingEquiv_linear_heq χ g A z).trans
      (TranslatedCoefficientValue.pullbackPullbackCongrEquiv_symm_linear_heq _ _ _ A _).symm
  have hM := fun (z : unitaryUnramifiedCharacters (normCharacters χ)) f k =>
    anchorChange_untwist_eval hback hG hK P A Aback (inverseComparison χ g A) z
      (zback (zg z)) (inverseTransport χ g hG A K hK P z) (inverseInducingEquiv χ g A z) (hE z)
      (inverseTransport_eq χ g hG A K hK P z) f k
  exact compactValue_const_of_eval hG K hK χback (changeAnchor hback P).cocharacter
    (changeAnchor hback P).centralizer_eq (changeAnchor hback P).iwasawa Aback
    χ P.cocharacter P.centralizer_eq P.iwasawa A
    (fun z => ActualCommonLeviV3.unitaryParameter χback (zback (zg z)))
    (ActualCommonLeviV3.unitaryParameter χ)
    (fun z => (inverseTransport χ g hG A K hK P z).toLinearMap) 1 K.one_mem
    (fun t => (TranslatedCoefficientValue.conjugateValue (1 : Gpts)
      (anchorMembership hback) A).symm
        (productCoefficientLeviEquiv (inverseComparison χ g A).symm t))
    (fun z f k => hM z f k) z z'

end InverseChart

section MultiplicationChart

variable (χ : Cochar) (s t : Gpts) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χt" => (χ ≫ (G.innerIso t).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χts" => (χt ≫ (G.innerIso s).hom)
set_option hygiene false in
set_option quotPrecheck false in
local notation "χst" => (χ ≫ (G.innerIso (s * t)).hom)
set_option hygiene false in
local notation "At" => conjugateRepresentation χ t A
set_option hygiene false in
local notation "Ats" => conjugateRepresentation χt s At
set_option hygiene false in
local notation "Ast" => conjugateRepresentation χ (s * t) A
set_option hygiene false in
local notation "zt" => ActualConjugateLeviV3.unitaryConjugateParameter χ t
set_option hygiene false in
local notation "zts" => ActualConjugateLeviV3.unitaryConjugateParameter χt s
set_option hygiene false in
local notation "zst" => ActualConjugateLeviV3.unitaryConjugateParameter χ (s * t)
set_option hygiene false in
local notation "hmul" => conjugationAnchor_mul χ s t

variable (R : ParabolicPresentation χst K)

/-- The transport between the twice-conjugated and the product-conjugated
displayed actual fibers. -/
abbrev multiplicationTransport (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    (fiber χts Ats K (changeAnchor (hmul).symm R) (zts (zt z))).representation.Equiv
      (fiber χst Ast K R (zst z)).representation := by
  with_reducible exact multiplicationEquiv χ s t hG A hK R z

/-- The twice-conjugated transport between the displayed fibers is the
same-Levi transport along `multiplicationInducingEquiv` followed by the inverse
product left translation by the identity point. -/
theorem multiplicationTransport_eq (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    letI := quotientCompact K hK R.cocharacter R.iwasawa
    letI := quotientCompact K hK (changeAnchor (hmul).symm R).cocharacter
      (changeAnchor (hmul).symm R).iwasawa
    multiplicationTransport χ s t hG A K hK R z = (by with_reducible_and_instances
      exact (ActualConjugateLeviTensor.coefficientCongr
          (fiberDecomposition (changeAnchor (hmul).symm R))
          (fiberRadicalClosed (changeAnchor (hmul).symm R))
          (radicalUnimodular (changeAnchor (hmul).symm R).cocharacter hG)
          (multiplicationInducingEquiv χ s t A z)).trans
        (CoefficientConjugation.leviCoefficientLeftTranslation
          (fiberDecomposition R) (fiberDecomposition (changeAnchor (hmul).symm R))
          1 (changeAnchor_parabolicMembership (hmul).symm R) (anchorMembership (hmul).symm)
          (changeAnchor_radicalMembership (hmul).symm R)
          (fiberRadicalClosed R) (fiberRadicalClosed (changeAnchor (hmul).symm R))
          (radicalUnimodular R.cocharacter hG)
          (radicalUnimodular (changeAnchor (hmul).symm R).cocharacter hG)
          (twistObject χst (ActualCommonLeviV3.unitaryParameter χst (zst z)) Ast)).symm) := by
  with_reducible_and_instances
    exact multiplicationEquiv_eq χ s t hG A hK R z

/-- The comparison of the product-conjugated representation, pulled back along
conjugation by the identity point, with the twice-conjugated representation. -/
def multiplicationComparison :
    ((@conjugationFunctor Gpts _ _ NonarchimedeanGroup.toIsTopologicalGroup 1 _ _
      (anchorMembership (hmul).symm)).obj Ast).representation.Equiv (Ats).representation :=
  TranslatedCoefficientValue.pullbackTwiceCongrEquiv (leviConjugation χ (s * t)).symm _
    (leviConjugation χ t).symm (leviConjugation χt s).symm A
    (fun n => (multiplication_point_eq χ s t n).symm)

/-- The twice-conjugated transport has a parameter-independent value in the
fixed compact charts. -/
theorem multiplicationTransport_chartValue_const
    (z z' : unitaryUnramifiedCharacters (normCharacters χ)) :
    chartValue
        (fun z => compactTensorEquiv χts hG K hK (changeAnchor (hmul).symm R).cocharacter
          (changeAnchor (hmul).symm R).centralizer_eq (changeAnchor (hmul).symm R).iwasawa Ats
          (ActualCommonLeviV3.unitaryParameter χts (zts (zt z))))
        (fun z => compactTensorEquiv χst hG K hK R.cocharacter R.centralizer_eq R.iwasawa Ast
          (ActualCommonLeviV3.unitaryParameter χst (zst z)))
        (fun z => (multiplicationTransport χ s t hG A K hK R z).toLinearMap) z =
      chartValue
        (fun z => compactTensorEquiv χts hG K hK (changeAnchor (hmul).symm R).cocharacter
          (changeAnchor (hmul).symm R).centralizer_eq (changeAnchor (hmul).symm R).iwasawa Ats
          (ActualCommonLeviV3.unitaryParameter χts (zts (zt z))))
        (fun z => compactTensorEquiv χst hG K hK R.cocharacter R.centralizer_eq R.iwasawa Ast
          (ActualCommonLeviV3.unitaryParameter χst (zst z)))
        (fun z => (multiplicationTransport χ s t hG A K hK R z).toLinearMap) z' := by
  have hE : ∀ z : unitaryUnramifiedCharacters (normCharacters χ),
      HEq (multiplicationInducingEquiv χ s t A z).toLinearEquiv
        (multiplicationComparison χ s t A).symm.toLinearEquiv := fun z =>
    (multiplicationInducingEquiv_linear_heq χ s t A z).trans
      (TranslatedCoefficientValue.pullbackTwiceCongrEquiv_symm_linear_heq _ _ _ _ A _).symm
  have hM := fun (z : unitaryUnramifiedCharacters (normCharacters χ)) f k =>
    anchorChange_untwist_eval (hmul).symm hG hK R Ast Ats (multiplicationComparison χ s t A)
      (zst z) (zts (zt z)) (multiplicationTransport χ s t hG A K hK R z)
      (multiplicationInducingEquiv χ s t A z) (hE z)
      (multiplicationTransport_eq χ s t hG A K hK R z) f k
  exact compactValue_const_of_eval hG K hK χts (changeAnchor (hmul).symm R).cocharacter
    (changeAnchor (hmul).symm R).centralizer_eq (changeAnchor (hmul).symm R).iwasawa Ats
    χst R.cocharacter R.centralizer_eq R.iwasawa Ast
    (fun z => ActualCommonLeviV3.unitaryParameter χts (zts (zt z)))
    (fun z => ActualCommonLeviV3.unitaryParameter χst (zst z))
    (fun z => (multiplicationTransport χ s t hG A K hK R z).toLinearMap) 1 K.one_mem
    (fun t' => (TranslatedCoefficientValue.conjugateValue (1 : Gpts)
      (anchorMembership (hmul).symm) Ast).symm
        (productCoefficientLeviEquiv (multiplicationComparison χ s t A).symm t'))
    (fun z f k => hM z f k) z z'

end MultiplicationChart

end Langlands.Plancherel.ActualConjugateLeviCoherence
