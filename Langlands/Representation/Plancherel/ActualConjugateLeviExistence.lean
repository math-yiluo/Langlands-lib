import Langlands.Representation.Plancherel.ActualConjugateLeviTranslationPreservation

/-! # Existence of the actual translated comparison -/

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
open ActualCommonLeviCoherence
open ActualConjugateLeviTwist ActualConjugateLeviFiberTransport
open ActualParabolicTranslation ActualParabolicUnitaryTranslation
open Langlands.HarishChandraSchwartz

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

omit [IsNonarchimedeanLocalField F] in
/-- Evaluation of a composite of an intertwining map with an equivalence. -/
theorem intertwiningComp_equiv_apply {k : Type*} {Γ : Type*} [CommSemiring k] [Monoid Γ]
    {V W X : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] {ρ : Representation k Γ V} {σ : Representation k Γ W}
    {τ : Representation k Γ X} (f : σ.IntertwiningMap τ) (e : ρ.Equiv σ) (v : V) :
    f.comp e.toIntertwiningMap v = f (e v) := rfl

/-- The translated family evaluates as the common-Levi family after the
unitary translation. -/
theorem ofCommonLevi_apply (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z v = U (zg z) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z v) :=
  intertwiningComp_equiv_apply (U (zg z)) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z) v

/-- The translated family is bijective at each unitary parameter. -/
theorem ofCommonLevi_bijective
    (dg : LeviNormalization χg Ag)
    (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (hU : ActualCommonLeviV3.PreservesCoefficientsAndForms χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa U)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) :
    Function.Bijective (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z) := by
  have hfun : ⇑(ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z) = ⇑(U (zg z)) ∘ ⇑(unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z) :=
    funext (ofCommonLevi_apply χ hG A K hK g P Q U z)
  rw [hfun]
  exact (hU (zg z)).1.comp (EquivLike.bijective _)

/-- The translated family preserves the published coefficient maps. -/
theorem ofCommonLevi_coefficientMap
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (hU : ActualCommonLeviV3.PreservesCoefficientsAndForms χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa U)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (E : (conjugateRepresentation χ (g : Gpts)
        (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation.Equiv
        (twistObject χg (ActualCommonLeviV3.unitaryParameter χg (zg z)) Ag).representation)
    (hE : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
      unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z =
        (Lg (ActualCommonLeviV3.unitaryParameter χ z)).trans (Ce E))
    (v : fiber χ A K P z) :
    coefficientMap χg hG Ag dg K hK Q (zg z) (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z v) =
      coefficientMap χ hG A d K hK P z v := by
  calc
    _ = coefficientMap χg hG Ag dg K hK Q (zg z) (U (zg z) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z v)) :=
      congrArg _ (ofCommonLevi_apply χ hG A K hK g P Q U z v)
    _ = coefficientMap χg hG Ag dg K hK (Pg) (zg z) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z v) := (hU (zg z)).2.1 _
    _ = _ := coefficientMap_of_eq_translated χ hG A K hK g P d dg z _ E hE v

/-- The translated family preserves the published forms for compatible
quotient Haar measures. -/
theorem ofCommonLevi_formalDegreeForm
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (hU : ActualCommonLeviV3.PreservesCoefficientsAndForms χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa U)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (hc : CompatibleHaar χ A K g d dg)
    (E : (conjugateRepresentation χ (g : Gpts)
        (twistObject χ (ActualCommonLeviV3.unitaryParameter χ z) A)).representation.Equiv
        (twistObject χg (ActualCommonLeviV3.unitaryParameter χg (zg z)) Ag).representation)
    (hE : letI := quotientCompact K hK P.cocharacter P.iwasawa
      letI := quotientCompact K hK (Pg).cocharacter (Pg).iwasawa
      unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z =
        (Lg (ActualCommonLeviV3.unitaryParameter χ z)).trans (Ce E))
    (v w : fiber χ A K P z) :
    (formalDegreeForm χg hG Ag dg K hK Q (zg z)).inner (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z v) (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z w) =
      (formalDegreeForm χ hG A d K hK P z).inner v w := by
  calc
    _ = (formalDegreeForm χg hG Ag dg K hK Q (zg z)).inner
          (U (zg z) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z v)) (U (zg z) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z w)) :=
      congrArg₂ _ (ofCommonLevi_apply χ hG A K hK g P Q U z v)
        (ofCommonLevi_apply χ hG A K hK g P Q U z w)
    _ = (formalDegreeForm χg hG Ag dg K hK (Pg) (zg z)).inner (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z v) (unitaryTranslation χ (g : Gpts) A K K hKK P hG hK hK z w) :=
      (hU (zg z)).2.2 _ _
    _ = _ := formalDegreeForm_of_eq_translated χ hG A K hK g P d dg hc z _ E hE v w

/-- The translated family preserves coefficients, the inducing equivalence
being the unitary conjugate-twist comparison. -/
theorem ofCommonLevi_coefficientMap_unitary
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (hU : ActualCommonLeviV3.PreservesCoefficientsAndForms χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa U)
    (z : unitaryUnramifiedCharacters (normCharacters χ)) (v : fiber χ A K P z) :
    coefficientMap χg hG Ag dg K hK Q (zg z) (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z v) =
      coefficientMap χ hG A d K hK P z v :=
  ofCommonLevi_coefficientMap χ hG A K hK g P d dg Q U hU z (unitaryTwistEquiv χ (g : Gpts) A z)
    (unitaryTranslation_eq χ (g : Gpts) A K K hKK P hG hK hK z) v

/-- The translated family preserves the forms, the inducing equivalence being
the unitary conjugate-twist comparison. -/
theorem ofCommonLevi_formalDegreeForm_unitary
    (d : LeviNormalization χ A) (dg : LeviNormalization χg Ag)
    (Q : ParabolicPresentation χg K)
    (U : ActualCommonLeviV3.UnitaryComparisonFamily χg Ag
      (Pg).cocharacter (Pg).centralizer_eq Q.cocharacter Q.centralizer_eq)
    (hU : ActualCommonLeviV3.PreservesCoefficientsAndForms χg hG Ag
      dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
      (Pg).cocharacter (Pg).centralizer_eq (Pg).iwasawa
      Q.cocharacter Q.centralizer_eq Q.iwasawa U)
    (z : unitaryUnramifiedCharacters (normCharacters χ))
    (hc : CompatibleHaar χ A K g d dg) (v w : fiber χ A K P z) :
    (formalDegreeForm χg hG Ag dg K hK Q (zg z)).inner (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z v) (ofCommonLevi χ (g : Gpts) A K K hKK P hG hK hK Q U z w) =
      (formalDegreeForm χ hG A d K hK P z).inner v w :=
  ofCommonLevi_formalDegreeForm χ hG A K hK g P d dg Q U hU z hc (unitaryTwistEquiv χ (g : Gpts) A z)
    (unitaryTranslation_eq χ (g : Gpts) A K K hKK P hG hK hK z) v w

end Translation

section Existence

variable (χ : Cochar) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup Gpts) (hK : IsCompact (K : Set Gpts)) (d : LeviNormalization χ A)

set_option maxHeartbeats 1600000 in
/-- Existence: the target-side common-Levi comparison of the closed
common-Levi coherence, preceded by the unitary translation, is an actual
translated comparison. -/
theorem existenceLaw (hd : HasSourceNormalization χ A d K) :
    ExistenceLaw χ hG A K hK d := by
  intro g dg P Q hc
  obtain ⟨⟨Sys, hSys, -, -, -⟩, -⟩ := ActualCommonLeviCoherence.closedCommonLeviCoherence
    _ hG _ dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK
    dg.splitCenter
  have hU := hSys (conjugatePresentation χ (g : Gpts) K K
    (RationalDynamicSource.conjugateCompact_eq_self (g : Gpts) K g.property) P) Q
  obtain ⟨-, -, -, -, -, -, -, -, hPCF⟩ := id hU
  refine ⟨⟨(by
    with_reducible
      exact ofCommonLevi χ (g : Gpts) A K K
        (RationalDynamicSource.conjugateCompact_eq_self (g : Gpts) K g.property) P hG hK hK Q
        (Sys _ Q)), ?_⟩⟩
  refine ⟨hd, hc, Sys _ Q, hU, (by with_reducible exact HEq.rfl), ?_⟩
  intro z
  refine ⟨?_, ?_, ?_⟩
  · with_reducible
      exact ofCommonLevi_bijective χ hG A K hK g P dg Q (Sys _ Q) hPCF z
  · intro v
    with_reducible
      exact ofCommonLevi_coefficientMap_unitary χ hG A K hK g P d dg Q (Sys _ Q) hPCF z v
  · intro v w
    with_reducible
      exact ofCommonLevi_formalDegreeForm_unitary χ hG A K hK g P d dg Q (Sys _ Q)
        hPCF z hc v w

end Existence

end Langlands.Plancherel.ActualConjugateLeviCoherence
