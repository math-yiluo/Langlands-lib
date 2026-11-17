import Langlands.Representation.Plancherel.ActualConjugateLeviTensor

noncomputable section

set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types true

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualConjugateLeviTwist

private theorem apply_eq_trans {X Y : Type*} (T : X → Y) {a b : X} {c : Y}
    (hab : a = b) (hbc : T b = c) : T a = c :=
  (congrArg T hab).trans hbc

section TranslationLaw

variable {H : Type u} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [NonarchimedeanGroup H] [SecondCountableTopology H]
  {P M U P' M' U' : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (k : IsSemidirectDecomposition P' M' U')
  (g : H) (hP : ∀ x : H, x ∈ P' ↔ g⁻¹ * x * g ∈ P)
  (hM : ∀ x : H, x ∈ M' ↔ g⁻¹ * x * g ∈ M)
  (hU' : ∀ x : H, x ∈ U' ↔ g⁻¹ * x * g ∈ U)
  (hc : IsClosed (U : Set H)) (hc' : IsClosed (U' : Set H))
  (hδ : IsUnimodularModulus U hc) (hδ' : IsUnimodularModulus U' hc')
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uW} ℂ M')
  (e : ((conjugationFunctor g hM).obj A).representation.Equiv B.representation)
  [CompactSpace (Induction.LeftQuotient P)] [CompactSpace (Induction.LeftQuotient P')]

private theorem coefficientCongr_after_translation_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h hc).obj A.contragredient) :
    coefficientCongr k hc' hδ' e
      (CoefficientConjugation.leviCoefficientLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A
        (leviNormalizedProductInductionTensorEquiv h h hc hc hδ hδ A A.contragredient
          (f ⊗ₜ[ℂ] ℓ))) =
      leviNormalizedProductInductionTensorEquiv k k hc' hc' hδ' hδ' B B.contragredient
        (CoefficientConjugation.leviInductionCongr k hc' hδ' e
          (CoefficientConjugation.leviLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A f) ⊗ₜ[ℂ]
          CoefficientConjugation.leviInductionCongr k hc' hδ'
            (A := ((conjugationFunctor g hM).obj A).contragredient)
            (B := B.contragredient) (smoothContragredientEquiv e.symm)
            (CoefficientConjugation.leviDualLeftTranslation h k g hP hM hU' hc hc' hδ hδ' A ℓ)) := by
  rw [CoefficientConjugation.leviCoefficientLeftTranslation_tmul, coefficientCongr_tmul]

end TranslationLaw

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : RationalPoint F G.X)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "gA" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "hg" => commonDecomposition χg χg rfl
set_option hygiene false in
local notation "hUg" => radical_isClosed χg
set_option hygiene false in
local notation "hδg" => DynamicOppositeCanonicalScalar.radical_unimodular χg hG

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

variable (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χg)
  (hψ'K' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K' gA)
  (q : ContinuedPair χg hG K' hK' ψ' hψ' hψ'K' χg rfl hχgK' (gA).contragredient)

variable (w : unramifiedCharacters (normCharacters χ))

set_option hygiene false in
local notation "Aw" => twistObject χ w A
set_option hygiene false in
local notation "Bw" => twistObject χg (conjugateParameter χ g w) gA
set_option hygiene false in
local notation "Cw" => (conjugationFunctor g (DynamicCoefficientConjugation.levi_mem_conjugation χ g)).obj Aw
set_option hygiene false in
local notation "ew" => conjugateTwistEquiv χ g w A
set_option hygiene false in
local notation "hp" => DynamicCoefficientConjugation.parabolic_mem_conjugation χ g
set_option hygiene false in
local notation "hm" => DynamicCoefficientConjugation.levi_mem_conjugation χ g
set_option hygiene false in
local notation "hu" => DynamicCoefficientConjugation.radical_mem_conjugation χ g
set_option hygiene false in
local notation "h0" => decomposition χ
set_option hygiene false in
local notation "hc0" => radical_isClosed χ
set_option hygiene false in
local notation "hd0" => DynamicOppositeCanonicalScalar.radical_unimodular χ hG

/-- Pure-tensor formula in the fully expanded actual translation and inducing
transport expression defining translatedCoefficient. -/
theorem translatedCoefficient_tmul
    (f : (DynamicNormalization.leviTwistedInductionFunctor h0 hc0).obj Aw)
    (ℓ : (DynamicNormalization.leviTwistedInductionFunctor h0 hc0).obj (Aw).contragredient) :
    letI : CompactSpace (LeftQuotient (parabolic χ)) :=
      ActualCommonLeviTensor.quotientCompact K hK χ hPK
    letI : CompactSpace (LeftQuotient (parabolic χg)) :=
      ActualCommonLeviTensor.quotientCompact K' hK' χg hχgK'
    coefficientCongr hg hUg hδg (A := Cw) (B := Bw) ew
      (CoefficientConjugation.leviCoefficientLeftTranslation h0 hg g hp hm hu hc0 hUg hd0 hδg Aw
        (leviNormalizedProductInductionTensorEquiv h0 h0 hc0 hc0 hd0 hd0 Aw (Aw).contragredient
          (f ⊗ₜ[ℂ] ℓ))) =
      leviNormalizedProductInductionTensorEquiv hg hg hUg hUg hδg hδg Bw (Bw).contragredient
        (CoefficientConjugation.leviInductionCongr hg hUg hδg (A := Cw) (B := Bw) ew
          (CoefficientConjugation.leviLeftTranslation h0 hg g hp hm hu hc0 hUg hd0 hδg Aw f) ⊗ₜ[ℂ]
          CoefficientConjugation.leviInductionCongr hg hUg hδg
            (A := (Cw).contragredient) (B := (Bw).contragredient)
            (smoothContragredientEquiv (ρ := (Bw).representation) (σ := (Cw).representation) (ew).symm)
            (CoefficientConjugation.leviDualLeftTranslation h0 hg g hp hm hu hc0 hUg hd0 hδg Aw ℓ)) := by
  have : CompactSpace (LeftQuotient (parabolic χ)) :=
    ActualCommonLeviTensor.quotientCompact K hK χ hPK
  have : CompactSpace (LeftQuotient (parabolic χg)) :=
    ActualCommonLeviTensor.quotientCompact K' hK' χg hχgK'
  exact coefficientCongr_after_translation_tmul h0 hg g hp hm hu hc0 hUg hd0 hδg Aw Bw ew f ℓ

variable (z : genericLocus χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q)

set_option hygiene false in
local notation "zg" => genericParameter χ g hG A K' hK' hχgK' ψ' hψ' hψ'K' p q z
set_option hygiene false in
local notation "Azg" => twistObject χg (zg).val gA
set_option hygiene false in
local notation "ht" => commonDecomposition χg ψ' hψ'
set_option hygiene false in
local notation "hUt" => radical_isClosed ψ'
set_option hygiene false in
local notation "hδt" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
set_option hygiene false in
local notation "Jz" => ContinuedPair.operator χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K'
  gA p ⟨(zg).val, (zg).property.choose.1⟩
set_option hygiene false in
local notation "Rz" => reverseDual χg hG K' hK' χg rfl hχgK' ψ' hψ' hψ'K'
  gA p q ⟨(zg).val, (zg).property.choose⟩
set_option hygiene false in
local notation "hz" => (zg).property.choose_spec.2
set_option hygiene false in
local notation "Cz" => ActualCommonLeviTensor.genericComparison χg hG K' hK' χg rfl hχgK'
  ψ' hψ' hψ'K' gA p q zg

/-- The same constructed comparison packaged as an equivalence on its
simultaneous regular and bijective locus. -/
def genericComparisonEquiv :=
  (translatedCoefficient χ g hG A K hK hPK z.val).trans
    ((Cz).ofBijective
      (ActualCommonLeviTensor.genericComparison_bijective χg hG K' hK' χg rfl hχgK'
        ψ' hψ' hψ'K' gA p q zg))

/-- Bijectivity for the exact two constructed factors of genericComparison. -/
theorem genericComparison_bijective :
    Function.Bijective (Cz ∘ translatedCoefficient χ g hG A K hK hPK z.val) :=
  (ActualCommonLeviTensor.genericComparison_bijective χg hG K' hK' χg rfl hχgK'
    ψ' hψ' hψ'K' gA p q zg).comp
      (translatedCoefficient χ g hG A K hK hPK z.val).bijective

end Langlands.Plancherel.ActualConjugateLeviTensor
