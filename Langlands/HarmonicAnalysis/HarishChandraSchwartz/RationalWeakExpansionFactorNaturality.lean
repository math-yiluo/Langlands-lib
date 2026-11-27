import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionFactorCompact

/-! # Naturality of a V.1 auxiliary c-integral -/

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

local instance factorNaturalityAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance factorNaturalityLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance factorNaturalityLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance factorNaturalityLeviFiniteType (J : Set (characterLattice T)) :
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
local instance factorNaturalityPointTopology : TopologicalSpace (rationalPoints M₀) :=
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
local notation "d₀" => commonDecomposition ψα θs hθ
set_option hygiene false in
local notation "d₁" => commonDecomposition ψα ψα rfl
set_option hygiene false in
local notation "u₀" => radical_isClosed θs
set_option hygiene false in
local notation "u₁" => radical_isClosed ψα
set_option hygiene false in
local notation "dₛ" => decomposition χs
set_option hygiene false in
local notation "uₛ" => radical_isClosed χs
set_option hygiene false in
local notation "hsq" => squaredModulus_of_centralSplitTorusCharacter ψα i (conjugatedCocharacter i ζ n) hθ
  (auxiliaryCocharacter i α (conjugatedCocharacter i ζ n)) rfl hCST hG hi
set_option hygiene false in
local notation "CRep(" V ")" => conjugateRep hG hi hν I I' hζ n hn α hα (V)
set_option hygiene false in
local notation "LRep(" V ")" => SmoothRep.pullback (eₛ).symm (V)
set_option hygiene false in
local notation "dom(" V ")" => FactorConverges hG hi hν I I' hζ n hn α hα K hK (CRep(V))
set_option hygiene false in
local notation "Γ(" V ")" => (normalizedInductionFunctor dM uM).obj (V)
set_option hygiene false in
local notation "Ind₀(" V ")" => (DynamicNormalization.leviTwistedInductionFunctor d₀ u₀).obj (CRep(V))
set_option hygiene false in
local notation "Ind₁(" V ")" => (DynamicNormalization.leviTwistedInductionFunctor d₁ u₁).obj (CRep(V))
set_option hygiene false in
local notation "Γₛ(" V ")" => (normalizedInductionFunctor dₛ uₛ).obj (LRep(V))
set_option hygiene false in
local notation "ι" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer θα) j hj hc
set_option hygiene false in
local notation "half" => HaarModulus.closedHalfCharacter (radical θα) (radical_isClosed θα)
  (DynamicOppositeStandardIntertwining.levi θα) (decomposition θα).levi_le_normalizer
set_option hygiene false in
local notation "qμ" => pairQuotientMeasure K hK θs ψα

variable {V W : SmoothRep.{0, u, uV} ℂ 𝐌}

/-- Change the inducing coefficients through the conjugation of the source Levi. -/
def cFactorConjugateInducingEquiv (e : V.representation.Equiv W.representation) :
    (CRep(V)).representation.Equiv (CRep(W)).representation :=
  CuspidalSupport.equivComp e (conjugationEquiv (n : rationalPoints G)
    (auxiliaryLevi_conj_iff hG hi hν I I' hζ n hn α hα)).toMonoidHom

/-- Change the inducing coefficients through the pullback to the lower Levi. -/
def cFactorLowerInducingEquiv (e : V.representation.Equiv W.representation) :
    (LRep(V)).representation.Equiv (LRep(W)).representation :=
  CuspidalSupport.equivComp e (eₛ).symm.toMonoidHom

set_option hygiene false in
local notation "ec(" e ")" => cFactorConjugateInducingEquiv hG hi hν I I' hζ n hn α hα (e)
set_option hygiene false in
local notation "es(" e ")" => cFactorLowerInducingEquiv hG hi hν I I' hζ n hn (e)
set_option hygiene false in
local notation "E₀(" e ")" => inducedMap d₀ u₀ (ec(e)).toIntertwiningMap
set_option hygiene false in
local notation "E₁(" e ")" => inducedMap d₁ u₁ (ec(e)).toIntertwiningMap
set_option hygiene false in
local notation "src(" e ")" => normalizedInductionEquivOfEquiv dM uM (e)
set_option hygiene false in
local notation "dst(" e ")" => normalizedInductionEquivOfEquiv dₛ uₛ (es(e))

/-- Both equivalent inducing representations have the same full convergence condition
for the auxiliary measure. -/
theorem cFactorConverges_iff_of_equiv (e : V.representation.Equiv W.representation) :
    dom(V) ↔ dom(W) :=
  domain_eq_top_iff_equiv d₀ u₀ (radical ψα) qμ (ec(e))

private def factorInputBeforeIntegral (V₀ : SmoothRep.{0, u, uV} ℂ 𝐌) : Γ(V₀) →ₗ[ℂ] Ind₀(V₀) :=
  (normalizedInductionLeviEquiv d₀ u₀ (radical_unimodular θs hG) (CRep(V₀))).toLinearMap ∘ₗ
    (factorTranslation hG hi hν I I' hζ n hn α hα V₀).toLinearMap

set_option hygiene false in
local notation "In(" V₀ ")" => factorInputBeforeIntegral hG hi hν I I' hζ n hn α hα V₀
set_option hygiene false in
local notation "J(" V₀ "," h ")" => factorIntertwiner hG hi hν I I' hζ n hn α hα K hK hCST (CRep(V₀)) (h)
set_option hygiene false in
local notation "CF(" V₀ "," h ")" => cFactor hG hi hν I I' hζ n hn α hα K hK hCST (V₀) (h)

private theorem factorInputBeforeIntegral_natural (e : V.representation.Equiv W.representation)
    (f : Γ(V)) : In(W) (src(e) f) = E₀(e) (In(V) f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rfl

private theorem factorIntegral_natural (e : V.representation.Equiv W.representation)
    (hV : dom(V)) (hW : dom(W)) (f : Ind₀(V)) :
    J(W, hW) (E₀(e) f) = E₁(e) (J(V, hV) f) := by
  have hnaturality := fullSourceIntertwiner_natural d₀ u₀ d₁ u₁ qμ (radicalHaar ψα K hK)
    (pairIntersectionHaar K hK θs ψα) (pairQuotientMeasure_isCompatible K hK θs ψα)
    (levi_isClosed ψα) hsq hV hW (ec(e)).toIntertwiningMap
  exact congrArg (fun m => m f) hnaturality

private def factorIntegralOutput (V₀ : SmoothRep.{0, u, uV} ℂ 𝐌) (hV : dom(V₀))
    (f : Γ(V₀)) : Ind₁(V₀) := J(V₀, hV) (In(V₀) f)

set_option hygiene false in
local notation "Out(" V₀ "," h ")" => factorIntegralOutput hG hi hν I I' hζ n hn α hα K hK hCST (V₀) (h)

private theorem cFactor_value (V₀ : SmoothRep.{0, u, uV} ℂ 𝐌) (hV : dom(V₀))
    (f : Γ(V₀)) (l : rationalPoints L) :
    ((CF(V₀, hV) f).1.1 l : V₀) = ((half (ι l))⁻¹ : ℂˣ) • (Out(V₀, hV) f).1.1 (ι l : rationalPoints G) := by
  let y := Out(V₀, hV) f
  let g := (normalizedInductionLeviEquiv d₁ u₁ (radical_unimodular ψα hG) (CRep(V₀))).symm y
  have he : ((CF(V₀, hV) f).1.1 l : V₀) =
      (factorRestriction hG hi hν I I' hζ n hn α hα (CRep(V₀)) g).1.1 l := rfl
  exact he.trans (factorRestriction_eval hG hi hν I I' hζ n hn α hα (CRep(V₀)) g l)

private theorem factorIntegralOutput_natural (e : V.representation.Equiv W.representation)
    (hV : dom(V)) (hW : dom(W)) (f : Γ(V)) :
    Out(W, hW) (src(e) f) = E₁(e) (Out(V, hV) f) := by
  change J(W, hW) (In(W) (src(e) f)) = E₁(e) (J(V, hV) (In(V) f))
  rw [factorInputBeforeIntegral_natural]
  exact factorIntegral_natural hG hi hν I I' hζ n hn α hα K hK hCST e hV hW (In(V) f)

/-- The actual c-factor commutes with a change of inducing representation, with the same
quotient integral and the canonical coefficient map on the lower induction. -/
theorem cFactor_natural (e : V.representation.Equiv W.representation)
    (hV : dom(V)) (hW : dom(W)) (f : Γ(V)) :
    CF(W, hW) (src(e) f) = dst(e) (CF(V, hV) f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext l
  have hCJ := factorIntegralOutput_natural hG hi hν I I' hζ n hn α hα K hK hCST e hV hW f
  let m : ℂˣ := (half (ι l))⁻¹
  let x : rationalPoints G := (ι l : rationalPoints G)
  let s : W := (Out(W, hW) (src(e) f)).1.1 x
  let t : V := (Out(V, hV) f).1.1 x
  have heval : s = e t := congrArg (fun (y : Ind₁(W)) => (y.1.1 x : W)) hCJ
  change ((CF(W, hW) (src(e) f)).1.1 l : W) = e ((CF(V, hV) f).1.1 l)
  have h₁ : ((CF(W, hW) (src(e) f)).1.1 l : W) = m • s :=
    cFactor_value hG hi hν I I' hζ n hn α hα K hK hCST W hW (src(e) f) l
  have h₂ : (m • s : W) = m • e t := congrArg (m • ·) heval
  have h₃ : (m • e t : W) = e (m • t) := (e.toLinearMap.map_smul (m : ℂ) t).symm
  have h₄ : (e (m • t) : W) = e ((CF(V, hV) f).1.1 l) :=
    congrArg (fun x : V => e x) (cFactor_value hG hi hν I I' hζ n hn α hα K hK hCST V hV f l).symm
  exact h₁.trans (h₂.trans (h₃.trans h₄))

end Langlands.HarishChandraSchwartz.WeakExpansion
