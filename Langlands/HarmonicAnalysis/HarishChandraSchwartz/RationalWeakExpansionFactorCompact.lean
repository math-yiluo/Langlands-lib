import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorParameters
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDynamicIwasawa
import Langlands.Representation.Plancherel.DynamicCommonLeviCompact
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport
import Langlands.Representation.Plancherel.CompactInductionGeneration
import Langlands.Representation.Plancherel.CompactOperatorDiagrams

/-! # An auxiliary c-integral on fixed compact pictures -/

noncomputable section

set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types true
set_option quotPrecheck false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

open Aubert.General Induction

section CompactLeftEvaluation

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H] [NonarchimedeanGroup H]
  {P M U : Subgroup H} (d : IsSemidirectDecomposition P M U) (K : OpenSubgroup H)
  (hU : IsClosed (U : Set H)) (hP : IsClosed (P : Set H)) (hK : IsCompact (K : Set H))
  (hPK : ∀ x : H, ∃ p : P, ∃ k : K, x = (p : H) * (k : H))
  {I : Type u} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous d.projection) (A : SmoothRep.{0, u, uV} ℂ M)

set_option hygiene false in
local notation "κ(" z ")" => unramifiedNormalizedInductionCompactEquiv d K hU hP hK hPK ν hν hr z A

/-- A fixed left translate of the compact subgroup lies in one Iwasawa product. The character
on the Levi component supplies its uniform scalar relative to the trivial twist. -/
theorem normalizedCompactExtension_leftTranslate (g : H) :
    ∃ c : unramifiedRegularFunctions ν,
      ∀ (z : unramifiedCharacters ν) (f : CompactInductionPicture d K A) (k : K),
        ((κ(z)).symm f).1.1 (g * k.val) = c.val z • ((κ(1)).symm f).1.1 (g * k.val) := by
  obtain ⟨p, l, hgl⟩ := hPK g
  let m := d.projection p
  refine ⟨unramifiedEvaluationRegular ν m, ?_⟩
  intro z f k
  let x : K := l * k
  have he : g * k.val = (p : H) * x.val := (congrArg (· * k.val) hgl).trans (mul_assoc _ _ _)
  rw [he]
  have hz := unramifiedNormalizedInductionCompactEquiv_symm_mul d K hU hP hK hPK ν hν hr z A f p x
  have h₁ := unramifiedNormalizedInductionCompactEquiv_symm_mul d K hU hP hK hPK ν hν hr 1 A f p x
  let h : ℂ := ↑(HaarModulus.closedHalfCharacter U hU P d.le_normalizer p)
  let v := A.representation m (eval _ _ f x)
  change ((κ(z)).symm f).1.1 ((p : H) * x.val) = h • ((z.val m : ℂˣ) : ℂ) • v at hz
  change ((κ(1)).symm f).1.1 ((p : H) * x.val) = h • (1 : ℂ) • v at h₁
  change _ = ((z.val m : ℂˣ) : ℂ) • _
  rw [hz, h₁, one_smul]
  exact smul_comm h ((z.val m : ℂˣ) : ℂ) (v : A)

end CompactLeftEvaluation

end Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open StandardIntertwining UnramifiedOperatorFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance factorCompactAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance factorCompactLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance factorCompactLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance factorCompactLeviFiniteType (J : Set (characterLattice T)) :
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
local instance factorCompactPointTopology : TopologicalSpace (rationalPoints M₀) :=
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

/-- Resolved convergence of one c-integral, in the original scheme character parameter. -/
def cFactorConvergenceRegion : Set X :=
  {z | FactorConverges hG hi hν I I' hζ n hn α hα K hK (A(Bz(B, z)))}

set_option hygiene false in
local notation "D" => cFactorConvergenceRegion hG hi hν I I' hζ n hn α hα K hK B
set_option hygiene false in
local notation "J" => pairFullDomainRegion ψα K hK θs hθ ψα (A(B))
set_option hygiene false in
local notation "qμ" => pairQuotientMeasure K hK θs ψα

include hG hi hν hζ hn hα in
/-- The actual integral uses the full convergence domain, transported along the scheme
character isomorphism with the same measure. -/
theorem cFactorConvergenceRegion_eq : D = par ⁻¹' J := by
  ext z
  exact domain_eq_top_iff_equiv d₀ u₀ (radical ψα) qμ (eqv(B, z))

/-- Transport a point and its convergence certificate to the actual pair domain. -/
def cFactorPairParameter (z : D) : J :=
  ⟨par z.val, (domain_eq_top_iff_equiv d₀ u₀ (radical ψα) qμ (eqv(B, z.val))).mp z.property⟩

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

private theorem factorInputLevi_eval (z : X) (f : SNorm(z)) (x : rationalPoints G) :
    ((((translateLevi(z))) f).1.1 x : B) = f.1.1 ((n : rationalPoints G)⁻¹ * x) :=
  rfl

private def factorInput (z : X) : CompactInductionPicture dM K B →ₗ[ℂ] SLevi(z) :=
  (origEta₀(z)).toLinearMap ∘ₗ (T(z)).toLinearMap ∘ₗ (κM(z)).symm.toLinearMap

set_option hygiene false in
local notation "factorIn" => factorInput hG hi hν I I' hζ n hn α hα K hK hPK B

/-- Compact left translation for one auxiliary factor at the actual normalizer lift. -/
def cFactorCompactTranslation (z : X) : CompactInductionPicture dM K B →ₗ[ℂ]
    CompactInductionPicture d₀ K (A(B)) :=
  (κ₀(z)).toLinearMap ∘ₗ (e₀(z)).toLinearMap ∘ₗ factorIn z

set_option hygiene false in
local notation "Lc" => cFactorCompactTranslation hG hi hν I I' hζ n hn α hα K hK hPK B

set_option hygiene false in
local notation "evalT" => compactEvalLinear d₀ K (A(B))

/-- Evaluation on the translated section in the auxiliary Levi-normalized model. -/
def cFactorCompactTranslationValue (z : X) (v : CompactInductionPicture dM K B) (k : K) : B :=
  (e₀(z) (factorIn z v)).1.1 (k : rationalPoints G)

set_option hygiene false in
local notation "LTval" => cFactorCompactTranslationValue hG hi hν I I' hζ n hn α hα K hK hPK B

/-- The compact translation is restriction of the translated section. -/
theorem cFactorCompactTranslationValue_eval (z : X) (v : CompactInductionPicture dM K B) (k : K) :
    evalT k (Lc z v) = LTval z v k :=
  rfl

section Lower

variable (K' : OpenSubgroup (rationalPoints L)) (hK' : IsCompact (K' : Set (rationalPoints L)))
  (hPK' : ∀ g : rationalPoints L, ∃ p : DynamicOppositeStandardIntertwining.parabolic χs,
    ∃ k : K', g = (p : rationalPoints L) * (k : rationalPoints L))

set_option hygiene false in
local notation "νₛ" => leviNormCharacters χs
set_option hygiene false in
local notation "sz(" z ")" => lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn (Φ z)
set_option hygiene false in
local notation "Bₛ" => SmoothRep.pullback (eₛ).symm B
set_option hygiene false in
local notation "dₛ" => decomposition χs
set_option hygiene false in
local notation "uₛ" => radical_isClosed χs
set_option hygiene false in
local notation "κₛ(" z ")" => unramifiedNormalizedInductionCompactEquiv dₛ K' uₛ
  (parabolic_isClosed χs) hK' hPK' νₛ (DynamicInducedOrbit.leviNormCharacters_continuous χs)
  (projection_continuous χs) (sz(z)) Bₛ
set_option hygiene false in
local notation "lowerEq(" z ")" => normalizedInductionEquivOfEquiv dₛ uₛ
  (twistPullbackEquiv hG hi hν I I' hζ n hn B (Φ z))
set_option hygiene false in
local notation "restrictEq(" z ")" => normalizedInductionEquivOfEquiv dₛ uₛ
  (restrictedConjugateEquiv hG hi hν I I' hζ n hn α hα (Bz(B, z)))
set_option hygiene false in
local notation "restrictInd(" z ")" =>
  factorRestriction hG hi hν I I' hζ n hn α hα (A(Bz(B, z)))
private def factorOutput (z : X) : TLevi(z) →ₗ[ℂ] CompactInductionPicture dₛ K' Bₛ :=
  (κₛ(z)).toLinearMap ∘ₗ (lowerEq(z)).toLinearMap ∘ₗ (restrictEq(z)).toLinearMap ∘ₗ
    (restrictInd(z)) ∘ₗ (origEta₁(z)).symm.toLinearMap

set_option hygiene false in
local notation "factorOut" => factorOutput hG hi hν I I' hζ n hn α hα B K' hK' hPK'

/-- Compact restriction through the lower Levi, with the outer normalization of `cFactor`. -/
def cFactorCompactRestriction (z : X) : CompactInductionPicture d₁ K (A(B)) →ₗ[ℂ]
    CompactInductionPicture dₛ K' Bₛ :=
  factorOut z ∘ₗ (e₁(z)).symm.toLinearMap ∘ₗ (κ₁(z)).symm.toLinearMap

set_option hygiene false in
local notation "Rc" => cFactorCompactRestriction hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK'
set_option hygiene false in
local notation "ι" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer θα) j hj hc
set_option hygiene false in
local notation "half" => HaarModulus.closedHalfCharacter (radical θα) (radical_isClosed θα)
  (DynamicOppositeStandardIntertwining.levi θα) (decomposition θα).levi_le_normalizer

/-- The V.1 stages restriction evaluates at the lower point and removes the outer half character. -/
theorem factorRestriction_eval
    (C : SmoothRep.{0, u, uV} ℂ (DynamicOppositeStandardIntertwining.levi ψα))
    (f : (normalizedInductionFunctor d₁ u₁).obj C) (l : rationalPoints L) :
    (factorRestriction hG hi hν I I' hζ n hn α hα C f).1.1 l =
      ((half (ι l))⁻¹ : ℂˣ) • f.1.1 (ι l : rationalPoints G) := by
  let S := RealizedLeviStages.inductionInStagesIso F hG θα j hj hc χs ψα hReal
    u₁ (radical_isClosed θα) (levi_isClosed θα)
  have he : (factorRestriction hG hi hν I I' hζ n hn α hα C f).1.1 l =
      ((SmoothRep.hom (S.app C).hom f).1.1 (1 : rationalPoints G)).1.1 l := rfl
  have hv := RealizedLeviStages.inductionInStagesIso_hom_eval F hG θα j hj hc χs ψα hReal
    u₁ (radical_isClosed θα) (levi_isClosed θα) C f 1 l
  refine Eq.trans (α := C) he (Eq.trans (α := C) hv ?_)
  exact congrArg (fun x : rationalPoints G => ((half (ι l))⁻¹ : ℂˣ) • f.1.1 x) (mul_one _)

set_option hygiene false in
local notation "unpack₁(" z "," v ")" =>
  (origEta₁(z)).symm ((e₁(z)).symm ((κ₁(z)).symm v))

set_option hygiene false in
local notation "AZ" z => Az(B, z)
set_option hygiene false in
local notation "YLevi" z => (DynamicNormalization.leviTwistedInductionFunctor d₁ u₁).obj (AZ z)

private theorem compactTarget_symm_eval (z : X) (v : CompactInductionPicture d₁ K (A(B))) (k : K) :
    (((κ₁(z)).symm v).1.1 (k : rationalPoints G) : B) = v.1.1 k :=
  eval_linearEquiv_symm (κ₁(z)) (fun (f : YLevi z) => (f.1.1 (k : rationalPoints G) : B))
    (fun w => w.1.1 k) (fun _ => rfl) v

private theorem unpackComparison_eval (z : X) (f : YLevi z) (g : rationalPoints G) :
    (((origEta₁(z)).symm ((e₁(z)).symm f)).1.1 g : B) = f.1.1 g :=
  rfl

private theorem factorUnpack_eval (z : X) (v : CompactInductionPicture d₁ K (A(B))) (k : K) :
    ((unpack₁(z, v)).1.1 (k : rationalPoints G) : B) = v.1.1 k :=
  (unpackComparison_eval hG hi hν I I' hζ n hn α hα B z ((κ₁(z)).symm v) (k : rationalPoints G)).trans
    (compactTarget_symm_eval hG hi hν I I' hζ n hn α hα K hK hPK B z v k)

private theorem cFactorCompactRestriction_raw_eval (z : X)
    (v : CompactInductionPicture d₁ K (A(B))) (k : K') :
    ((Rc z v).1.1 k : B) = (restrictInd(z) (unpack₁(z, v))).1.1 (k : rationalPoints L) :=
  rfl

set_option maxHeartbeats 1200000 in
/-- At each lower compact point, only the original compact value and the outer half character
enter the stages restriction. -/
theorem cFactorCompactRestriction_eval
    (hKL : ∀ k : K', ((ι (k : rationalPoints L)) : rationalPoints G) ∈ K)
    (z : X) (v : CompactInductionPicture d₁ K (A(B))) (k : K') :
    ((Rc z v).1.1 k : B) =
      ((half (ι (k : rationalPoints L)))⁻¹ : ℂˣ) • (v.1.1 ⟨_, hKL k⟩ : B) := by
  let kG : K := ⟨_, hKL k⟩
  have hraw := cFactorCompactRestriction_raw_eval hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK' z v k
  have hst := factorRestriction_eval hG hi hν I I' hζ n hn α hα (A(Bz(B, z))) (unpack₁(z, v)) (k : rationalPoints L)
  have he := factorUnpack_eval hG hi hν I I' hζ n hn α hα K hK hPK B z v kG
  exact hraw.trans (hst.trans (congrArg (fun w : B => ((half (ι (k : rationalPoints L)))⁻¹ : ℂˣ) • w) he))

/-- Once the lower compact maps to the ambient compact, restriction is a fixed linear map. -/
theorem cFactorCompactRestriction_eq
    (hKL : ∀ k : K', ((ι (k : rationalPoints L)) : rationalPoints G) ∈ K) (z w : X) :
    Rc z = Rc w := by
  ext v k
  exact (cFactorCompactRestriction_eval hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK'
    hKL z v k).trans
    (cFactorCompactRestriction_eval hG hi hν I I' hζ n hn α hα K hK hPK B K' hK' hPK'
      hKL w v k).symm

/-- Read the actual single-factor map on the source and lower fixed compact pictures. -/
def cFactorOnCompact (z : D) : CompactInductionPicture dM K B →ₗ[ℂ]
    CompactInductionPicture dₛ K' Bₛ :=
  (κₛ(z.val)).toLinearMap ∘ₗ (lowerEq(z.val)).toLinearMap ∘ₗ
    cFactor hG hi hν I I' hζ n hn α hα K hK hCST (Bz(B, z.val)) z.property ∘ₗ
    (κM(z.val)).symm.toLinearMap

set_option hygiene false in
local notation "Jc" => compactFamily ψα hG K hK θs hθ f₀ ψα rfl f₁ hsq (A(B))

include hG hi hν hζ hn hα in
/-- The actual factor is the compact standard integral between compact translation and lower
restriction. The full-domain equivalence transports the original convergence witness. -/
theorem cFactorOnCompact_eq (z : D) :
    cFactorOnCompact hG hi hν I I' hζ n hn α hα K hK hPK hCST B K' hK' hPK' z =
      Rc z.val ∘ₗ Jc (cFactorPairParameter hG hi hν I I' hζ n hn α hα K hK B z) ∘ₗ Lc z.val := by
  let Z := z.val
  let w := cFactorPairParameter hG hi hν I I' hζ n hn α hα K hK B z
  let J₀ := factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST (CConj(Z)) z.property
  let J₁ := pairFamily ψα K hK θs hθ ψα rfl hsq (A(B)) w
  have he : ∀ v : SLevi(Z), J₁ (e₀(Z) v) = e₁(Z) (J₀ v) := by
    intro v
    have hw := fullSourceIntertwiner_natural d₀ u₀ d₁ u₁ qμ (radicalHaar ψα K hK)
      (pairIntersectionHaar K hK θs ψα) (pairQuotientMeasure_isCompatible K hK θs ψα)
      (levi_isClosed ψα) hsq z.property w.property (eqv(B, Z)).toIntertwiningMap
    exact congrArg (fun m => m v) hw
  exact compactOperatorOfSquare (factorIn Z) (factorOut Z) J₀.toLinearMap J₁.toLinearMap
    (e₀(Z)) (e₁(Z)) (κ₀(Z)) (κ₁(Z)) he

end Lower

end Langlands.HarishChandraSchwartz.WeakExpansion
