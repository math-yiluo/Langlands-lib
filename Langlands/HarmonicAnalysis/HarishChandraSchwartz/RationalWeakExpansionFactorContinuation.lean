import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorCompact
import Langlands.Representation.Plancherel.DynamicCommonLeviOpenPolePresentation
import Langlands.Representation.Plancherel.RationalOperatorContinuationAlgebra

/-! # Rational continuation of an auxiliary c-factor -/

noncomputable section

set_option maxHeartbeats 650000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

section CompactEvaluation

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H} (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
  (hU : IsClosed (U : Set H)) (hP : IsClosed (P : Set H)) (hK : IsCompact (K : Set H))
  (hPK : ∀ x : H, ∃ p : P, ∃ k : K, x = (p : H) * (k : H))
  {I : Type u} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous d.projection) (A : SmoothRep.{0, u, uV} ℂ M)

/-- Evaluate an Iwasawa extension along a fixed translate of the compact subgroup. -/
def normalizedCompactTranslatedValue (g : H) (z : unramifiedCharacters ν)
    (f : CompactInductionPicture d K A) (k : K) : A :=
  ((unramifiedNormalizedInductionCompactEquiv d K hU hP hK hPK ν hν hr z A).symm f).1.1 (g * k.val)

private theorem normalizedCompactTranslatedValue_monomial (g : H) :
    ∃ c : unramifiedRegularFunctions ν, ∀ z f k,
      normalizedCompactTranslatedValue d K hU hP hK hPK ν hν hr A g z f k =
        c.val z • normalizedCompactTranslatedValue d K hU hP hK hPK ν hν hr A g 1 f k :=
  normalizedCompactExtension_leftTranslate d K hU hP hK hPK ν hν hr A g

end CompactEvaluation

section ReparametrizeTranslation

variable {H H' : Type u} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']
  {I : Type u} (ν : I → (H →* ℝ≥0ˣ)) (e : H ≃ₜ* H')
  {V W Z Q : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]

local notation "Φ" => unramifiedCharactersHomeomorph e ν
local notation "X" => unramifiedCharacters ν
local notation "Y" => unramifiedCharacters (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom)

private theorem isPolynomialOperatorOn_of_translated_values
    (L : X → V →ₗ[ℂ] W) (g : Y → V → Q → Z)
    (ev : Q → W →ₗ[ℂ] Z)
    (hext : ∀ {f g}, (∀ k, ev k f = ev k g) → f = g)
    (hL : ∀ z v k, ev k (L z v) = g (Φ z) v k)
    (hg : ∃ c : unramifiedRegularFunctions (fun i => (ν i).comp e.symm.toMulEquiv.toMonoidHom),
      ∀ z v k, g z v k = c.val z • g 1 v k) :
    IsPolynomialOperatorOn Set.univ (fun z => L z.val) := by
  obtain ⟨c, hc⟩ := hg
  let b := (unramifiedRegularFunctionsEquiv e ν).symm c
  have hvalue (z : X) : b.val z = c.val (Φ z) :=
    unramifiedRegularFunctionsEquiv_symm_apply e ν c z
  refine isPolynomialOperatorOn_of_pointwise_regular_smul ev hext 1 b hL ?_
  intro z v k
  rw [map_one, hvalue]
  exact hc (Φ z) v k

end ReparametrizeTranslation

section ChangeParameter

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

local instance parameterPointTopology (J : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine J.X.left] : TopologicalSpace (rationalPoints J) := rationalPointTopology F J.X

set_option hygiene false in
local notation "X(" J ")" => unramifiedCharacters (fun a => (rationalNormCharacters J a).toMul)

private def continuationWithPoles_parameterPullback (e : G ≅ H)
    {U : Set X(G)} {D S : Set X(H)} (hU : U ⊆ rationalUnramifiedCharacterTransport e ⁻¹' D)
    (hD : D ⊆ S) (A : S → V →ₗ[ℂ] W) (s : U → S)
    (hs : ∀ z : U, (s z).val = rationalUnramifiedCharacterTransport e z.val)
    (p : Σ p : RationalOperatorContinuationData D (fun z => A ⟨z.val, hD z.property⟩),
      RationalOperatorPolePresentation H p.denominator p.numerator) :
    Σ p : RationalOperatorContinuationData U (fun z => A (s z)),
      RationalOperatorPolePresentation G p.denominator p.numerator := by
  let q := (p.1.parameterPullback e).restrict hU
  exact ⟨q.ofFamilyEq (fun z => congrArg A (Subtype.ext (hs z).symm)), p.2.parameterPullback e⟩

end ChangeParameter
end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open DynamicCommonLeviPresentations StandardIntertwining UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance factorContinuationAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance factorContinuationLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance factorContinuationLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance factorContinuationLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

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
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

variable (α : cocharacterLattice T)
  (hα : Dynamic.centralizer (CommGroupScheme.groupHom α ≫ i) = standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐌" => RationalPointFamily.levi i ν I
set_option hygiene false in
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "ψα" =>
  CommGroupScheme.groupHom (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) ≫ i
set_option hygiene false in
local notation "θs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
local instance factorContinuationPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

set_option hygiene false in
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
set_option hygiene false in
local notation "Φ" => unramifiedCharactersHomeomorph (leviRationalPointHomeomorph i ν I) ν₀

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (hCST : CentralSplitTorusCharacterStatement.{u})

set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "j" => Standard.leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "L" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "θα" => CommGroupScheme.groupHom α ≫ i
set_option hygiene false in
local notation "hj" => outer_isRepresentedBy (i := i) (ν := ν) I' α hα
set_option hygiene false in
local notation "hc" => Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "hReal" => auxiliary_realization hG hi hν I I' hζ n hn α hα
set_option hygiene false in
local notation "hθ" => (centralizer_auxiliary hG hi hν I I' hζ n hn α hα).symm
set_option hygiene false in
local notation "dM" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "uM" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "pM" => isClosed_standardParabolicPoints_rootSet hG hi hν I
set_option hygiene false in
local notation "fM" => factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
set_option hygiene false in
local notation "rM" => continuous_projection_standard hG hi hν (rootSet_subset i ν I) _
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "d₀" => commonDecomposition ψα θs hθ
set_option hygiene false in
local notation "d₁" => commonDecomposition ψα ψα rfl
set_option hygiene false in
local notation "u₀" => radical_isClosed θs
set_option hygiene false in
local notation "u₁" => radical_isClosed ψα
set_option hygiene false in
local notation "f₀" => factorization_subtype (isIwasawaPair_dynamicParabolic_of_minimal hG hi hν hPK θs)
set_option hygiene false in
local notation "f₁" => factorization_subtype (isIwasawaPair_dynamicParabolic_of_minimal hG hi hν hPK ψα)
set_option hygiene false in
local notation "hsq" => squaredModulus_of_centralSplitTorusCharacter ψα i (conjugatedCocharacter i ζ n) hθ
  (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) rfl hCST hG hi
set_option hygiene false in
local notation "par" => rationalUnramifiedParameterHomeomorph (factorParameterIso hG hi hν I I' hζ n hn α hα).symm
set_option hygiene false in
local notation "νA" => normCharacters ψα
set_option hygiene false in
local notation "X" => unramifiedCharacters ν₀
set_option hygiene false in
local notation "Y" => unramifiedCharacters νA
set_option hygiene false in
local notation "t(" z ")" => parameterTransport ψα (par z)
set_option hygiene false in
local notation "A(" B ")" => conjugateRep hG hi hν I I' hζ n hn α hα B
set_option hygiene false in
local notation "Bz(" B "," z ")" => (B).twist (Φ z).val.toMonoidHom (unramifiedCharacter_isOpen_ker νM (Φ z))
set_option hygiene false in
local notation "Az(" B "," z ")" => (A(B)).twist (t(z)).val.toMonoidHom
  (unramifiedCharacter_isOpen_ker (leviNormCharacters ψα) (t(z)))
set_option hygiene false in
local notation "eqv(" B "," z ")" => factorConjugateTwistEquiv hG hi hν I I' hζ n hn α hα B z

variable (B : SmoothRep.{0, u, uV} ℂ 𝐌)

set_option hygiene false in
local notation "κM(" z ")" => unramifiedNormalizedInductionCompactEquiv dM K uM pM hK fM νM
  (continuous_leviRationalNormCharacters i ν I) rM (Φ z) B
set_option hygiene false in
local notation "κ₀(" z ")" => compactEquiv ψα hG K hK θs hθ f₀ (par z) (A(B))
set_option hygiene false in
local notation "κ₁(" z ")" => compactEquiv ψα hG K hK ψα rfl f₁ (par z) (A(B))
set_option hygiene false in
local notation "η₀(" z ")" => normalizedInductionLeviEquiv d₀ u₀ (radical_unimodular θs hG) (Az(B, z))
set_option hygiene false in
local notation "η₁(" z ")" => normalizedInductionLeviEquiv d₁ u₁ (radical_unimodular ψα hG) (Az(B, z))
set_option hygiene false in
local notation "T(" z ")" => factorTranslation hG hi hν I I' hζ n hn α hα (Bz(B, z))

set_option hygiene false in
local notation "D" => cFactorConvergenceRegion hG hi hν I I' hζ n hn α hα K hK B
set_option hygiene false in
local notation "J" => pairFullDomainRegion ψα K hK θs hθ ψα (A(B))
set_option hygiene false in
local notation "qμ" => pairQuotientMeasure K hK θs ψα

set_option hygiene false in
local notation "CConj(" z ")" => A(Bz(B, z))
set_option hygiene false in
local notation "SLevi(" z ")" => (DynamicNormalization.leviTwistedInductionFunctor d₀ u₀).obj (CConj(z))
set_option hygiene false in
local notation "TLevi(" z ")" => (DynamicNormalization.leviTwistedInductionFunctor d₁ u₁).obj (CConj(z))
set_option hygiene false in
local notation "e₀(" z ")" => inducedLeviLinearEquiv d₀ u₀ (eqv(B, z))
set_option hygiene false in
local notation "e₁(" z ")" => inducedLeviLinearEquiv d₁ u₁ (eqv(B, z))
set_option hygiene false in
local notation "origEta₀(" z ")" => normalizedInductionLeviEquiv d₀ u₀ (radical_unimodular θs hG) (CConj(z))
set_option hygiene false in
local notation "origEta₁(" z ")" => normalizedInductionLeviEquiv d₁ u₁ (radical_unimodular ψα hG) (CConj(z))

set_option hygiene false in
local notation "SNorm(" z ")" => (normalizedInductionFunctor dM uM).obj (Bz(B, z))
set_option hygiene false in
local notation "translateLevi(" z ")" => (e₀(z)).toLinearMap ∘ₗ (origEta₀(z)).toLinearMap ∘ₗ (T(z)).toLinearMap

private theorem factorTranslatedSection_eval (z : X) (f : SNorm(z)) (x : rationalPoints G) :
    ((((translateLevi(z))) f).1.1 x : B) = f.1.1 ((n : rationalPoints G)⁻¹ * x) :=
  rfl

set_option hygiene false in
local notation "Lc" => cFactorCompactTranslation hG hi hν I I' hζ n hn α hα K hK hPK B
set_option hygiene false in
local notation "Lvalue" => cFactorCompactTranslationValue hG hi hν I I' hζ n hn α hα K hK hPK B
set_option hygiene false in
local notation "ValExt" => normalizedCompactTranslatedValue dM K uM pM hK fM νM
  (continuous_leviRationalNormCharacters i ν I) rM B (n : rationalPoints G)⁻¹

private theorem compactTranslationValue_eq (z : X) (v : CompactInductionPicture dM K B) (k : K) :
    Lvalue z v k = ValExt (Φ z) v k :=
  factorTranslatedSection_eval hG hi hν I I' hζ n hn α hα B z ((κM(z)).symm v) (k : rationalPoints G)

private def translatedCompactEval (k : K) : CompactInductionPicture d₀ K (A(B)) →ₗ[ℂ] B :=
  compactEvalLinear d₀ K (A(B)) k

private theorem compactTranslation_eval_normalized (z : X) (v : CompactInductionPicture dM K B) (k : K) :
    translatedCompactEval hG hi hν I I' hζ n hn α hα K B k (Lc z v) = ValExt (Φ z) v k :=
  (cFactorCompactTranslationValue_eval hG hi hν I I' hζ n hn α hα K hK hPK B z v k).trans
    (compactTranslationValue_eq hG hi hν I I' hζ n hn α hα K hK hPK B z v k)

/-- The compact translation at the actual normalizer lift is a polynomial operator family. -/
theorem cFactorCompactTranslation_polynomial :
    IsPolynomialOperatorOn Set.univ (fun z => Lc z.val) :=
  isPolynomialOperatorOn_of_translated_values ν₀ (leviRationalPointHomeomorph i ν I)
    Lc ValExt (translatedCompactEval hG hi hν I I' hζ n hn α hα K B)
    (fun h => compactPicture_ext d₀ K (A(B)) h)
    (compactTranslation_eval_normalized hG hi hν I I' hζ n hn α hα K hK hPK B)
    (normalizedCompactTranslatedValue_monomial dM K uM pM hK fM νM
      (continuous_leviRationalNormCharacters i ν I) rM B (n : rationalPoints G)⁻¹)

section Continuation

set_option hygiene false in
local notation "Jc" => compactFamily ψα hG K hK θs hθ f₀ ψα rfl f₁ hsq (A(B))
set_option hygiene false in
local notation "E" => (factorParameterIso hG hi hν I I' hζ n hn α hα).symm

variable {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (hUD : U ⊆ D)

set_option hygiene false in
local notation "V" => (par) '' U

include hU in
private theorem factorAuxiliaryDomain_open : IsOpen V := (par).isOpenMap _ hU

include hne in
private theorem factorAuxiliaryDomain_nonempty : (V : Set Y).Nonempty := hne.image (par)

include hUD in
private theorem factorAuxiliaryDomain_subset : V ⊆ J :=
  Set.image_subset_iff.mpr (hUD.trans
    (cFactorConvergenceRegion_eq hG hi hν I I' hζ n hn α hα K hK B).subset)

set_option hygiene false in
local notation "hVJ" => factorAuxiliaryDomain_subset hG hi hν I I' hζ n hn α hα K hK B hUD
set_option hygiene false in
local notation "Jfirst" => fun z : (V : Set Y) => Jc ⟨z.val, hVJ z.property⟩

include hU hne in
set_option backward.isDefEq.respectTransparency.types false in
private def factorAuxiliaryContinuation
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))} (sc : Tc.toGrp ⟶ M₀) (hsc : IsSplitComponent sc)
    (hiB : B.IsIrreducible) (hB : B.IsAdmissible) :
    Σ p : RationalOperatorContinuationData V Jfirst,
      RationalOperatorPolePresentation (parameterScheme ψα) p.denominator p.numerator := by
  let e := conjugationEquiv (n : rationalPoints G) (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)
  have hiA : (A(B)).IsIrreducible := (isIrreducible_comp_continuousMulEquiv_iff B.representation e).mpr hiB
  have hA : (A(B)).IsAdmissible := isAdmissible_comp_continuousMulEquiv B.representation e hB
  exact pairContinuationWithPolesOfOpenSubset ψα hG (hsc.comp_iso E) K hK
    ⟨θs, hθ⟩ ⟨ψα, rfl⟩ f₀ f₁ hsq (A(B)) hiA hA hVJ
    (factorAuxiliaryDomain_open hG hi hν I I' hζ n hn α hα hU)
    (factorAuxiliaryDomain_nonempty hG hi hν I I' hζ n hn α hα hne)

private theorem factorDomain_in_pullback : U ⊆ rationalUnramifiedCharacterTransport E ⁻¹' V :=
  fun z hz => ⟨z, hz, rfl⟩

set_option hygiene false in
local notation "PairArg" => cFactorPairParameter hG hi hν I I' hζ n hn α hα K hK B
set_option hygiene false in
local notation "subPar" => fun z : U => PairArg ⟨z.val, hUD z.property⟩
set_option hygiene false in
local notation "Joriginal" => fun z : U => Jc (subPar z)

private theorem cFactorPairParameter_val (x : D) :
    (PairArg x).val = rationalUnramifiedCharacterTransport E x.val :=
  rfl

include hU hne in
set_option backward.isDefEq.respectTransparency.types false in
private def factorContinuationOnScheme
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))} (sc : Tc.toGrp ⟶ M₀) (hsc : IsSplitComponent sc)
    (hiB : B.IsIrreducible) (hB : B.IsAdmissible) :
    Σ p : RationalOperatorContinuationData U Joriginal,
      RationalOperatorPolePresentation M₀ p.denominator p.numerator :=
  continuationWithPoles_parameterPullback E
    (factorDomain_in_pullback hG hi hν I I' hζ n hn α hα)
    hVJ Jc subPar
    (fun z => cFactorPairParameter_val hG hi hν I I' hζ n hn α hα K hK B ⟨z.val, hUD z.property⟩)
    (factorAuxiliaryContinuation hG hi hν I I' hζ n hn α hα K hK hPK hCST B hU hne hUD sc hsc hiB hB)

variable (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))
  (hPK' : ∀ g : rationalPoints L, ∃ p : DynamicOppositeStandardIntertwining.parabolic χs,
    ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))

set_option hygiene false in
local notation "Rc" => cFactorCompactRestriction hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK'
set_option hygiene false in
local notation "ι" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer θα) j hj hc
set_option hygiene false in
local notation "factorCompact" => cFactorOnCompact hG hi hν I I' hζ n hn α hα K hK hPK hCST B K' hK' hPK'

include hU hne in
set_option maxHeartbeats 900000 in
/-- On a nonempty open convergence region, the actual fixed compact factor has a denominator
clearing its whole operator and a second, unitary-factored pole presentation. -/
theorem exists_cFactorOnCompactContinuationWithPoles
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))} (sc : Tc.toGrp ⟶ M₀) (hsc : IsSplitComponent sc)
    (hiB : B.IsIrreducible) (hB : B.IsAdmissible)
    (hKL : ∀ k : K', ((ι (k : rationalPoints L)) : rationalPoints G) ∈ K) :
    ∃ p : RationalOperatorContinuationData U (fun z => factorCompact ⟨z.val, hUD z.property⟩),
      Nonempty (RationalOperatorPolePresentation M₀ p.denominator p.numerator) := by
  let p := factorContinuationOnScheme hG hi hν I I' hζ n hn α hα K hK hPK hCST B hU hne hUD sc hsc hiB hB
  have hL := cFactorCompactTranslation_polynomial hG hi hν I I' hζ n hn α hα K hK hPK B
  let q := p.1.composePolynomial Lc (Rc 1) hL
  have heq (z : U) : (Rc 1) ∘ₗ Joriginal z ∘ₗ Lc z.val = factorCompact ⟨z.val, hUD z.property⟩ := by
    rw [cFactorOnCompact_eq]
    exact congrArg (fun R => R ∘ₗ Joriginal z ∘ₗ Lc z.val)
      (cFactorCompactRestriction_eq hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK' hKL 1 z.val)
  exact ⟨q.ofFamilyEq heq, ⟨p.2.composePolynomial M₀ Lc (Rc 1) hL⟩⟩

end Continuation

end Langlands.HarishChandraSchwartz.WeakExpansion
