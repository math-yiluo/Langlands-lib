import Langlands.Representation.Plancherel.ActualCommonLeviTensor
import Langlands.Representation.Plancherel.DynamicOppositeUniformNonvanishing
import Langlands.Representation.Intertwining.PQCompositionBruhatOrder
import Mathlib.RepresentationTheory.Irreducible

/-! # Nonvanishing of the continued actual common-Levi standard operator -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicOppositeNonvanishing DynamicCommonLeviComposition DynamicCommonLeviCompact
open DynamicCommonLeviContinuation UnramifiedOperatorFamily

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
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)

include hG hψ hψ' in
omit [LocallyOfFiniteType G.X.hom] in
/-- An Iwahori factorization for the source and its opposite gives the local
product on the target radical, using its common-centralizer product chart. -/
theorem hasSourceLocalProduct_of_commonCentralizer
    (Q : OpenSubgroup (RationalPoint F G.X)) (hfac : HasOppositeIwahoriFactorization ψ Q) :
    HasSourceLocalProduct (parabolic ψ) (radical ψ) (radical ψ') Q := by
  let := hG.smooth
  have hZ : (Dynamic.centralizer ψ').carrier (Over.mk (𝟙 _)) =
      (Dynamic.centralizer ψ).carrier (Over.mk (𝟙 _)) := by rw [hψ', hψ]
  intro x hx hPx
  obtain ⟨p₀, hp₀, k, hk, hxk⟩ := hPx
  obtain ⟨a, ha, b, hb, hxab⟩ :=
    Aubert.General.RepresentedParabolic.exists_mul_eq_of_secondChart hZ hx
  obtain ⟨o, ho, m, hm, w, hw, hoQ, _, hk'⟩ := hfac k⁻¹ (Q.inv_mem hk)
  have hko : k * o = w⁻¹ * m⁻¹ := by
    have hk₂ : k = (o * m * w)⁻¹ := by rw [← hk', inv_inv]
    rw [hk₂]
    group
  have hxo : x * o ∈ parabolic ψ := by
    rw [hxk, mul_assoc, hko]
    exact mul_mem hp₀ (mul_mem (inv_mem ((decomposition ψ).unipotent_le hw))
      (inv_mem ((decomposition ψ).levi_le hm)))
  have hbo : b * o ∈ parabolic ψ := by
    have h := mul_mem (inv_mem ((decomposition ψ).unipotent_le ha)) hxo
    simpa only [hxab, mul_assoc, inv_mul_cancel_left] using h
  have ho' : b * o = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic ψ (mul_mem hb.1 ho) hbo
  have hbQ : b ∈ Q := by
    rw [eq_inv_of_mul_eq_one_left ho']
    exact Q.inv_mem hoQ
  exact ⟨a, ha, b, hbQ, hb.2, hxab⟩

local notation "h₀" => commonDecomposition χ ψ hψ
local notation "h₁" => commonDecomposition χ ψ' hψ'
local notation "hU₀" => radical_isClosed ψ
local notation "hU₁" => radical_isClosed ψ'
local notation "hδ₀" => DynamicOppositeCanonicalScalar.radical_unimodular ψ hG
local notation "hδ₁" => DynamicOppositeCanonicalScalar.radical_unimodular ψ' hG
local notation "hP₀" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ
local notation "hP₁" => DynamicOppositeCanonicalScalar.parabolic_isClosed ψ'
local notation "hr₀" => commonProjection_continuous χ ψ hψ
local notation "hr₁" => commonProjection_continuous χ ψ' hψ'
local notation "ν" => leviNormCharacters χ
set_option quotPrecheck false in
local notation "hν" => (fun a => (DynamicOppositeCanonicalScalar.normCharacters_continuous χ a).comp
  (parameterHomeomorph χ).symm.continuous)
local notation "μquot" => pairQuotientMeasure K hK ψ ψ'

/-- At every regular parameter the same compact test section realizes a
fixed nonzero multiple of the chosen inducing vector at the identity. -/
theorem exists_continuedPair_eval_one_eq (v : A) :
    ∃ e : CompactInductionPicture h₀ K A, ∃ c : ℂ, c ≠ 0 ∧ ∀ z : p.regularRegion,
      compactPictureEvalOne h₁ K A (p.presentation.continuedOperator z e) = c • v := by
  obtain ⟨S, hS⟩ := A.isSmooth v
  obtain ⟨W, hW, hWQ⟩ := exists_nhds_fixedVectors_comp_projection h₀ hr₀ A.representation S v hS
  obtain ⟨Q, hQc, hQW, hfac⟩ := exists_factored_compactOpen_subset ψ hG
    (Filter.inter_mem hW (K.isOpen.mem_nhds K.one_mem))
  have hQK : (Q : Set (RationalPoint F G.X)) ⊆ K := fun x hx => (hQW hx).2
  have hv := hWQ Q fun x hx => (hQW hx).1
  have hloc := hasSourceLocalProduct_of_commonCentralizer χ hG ψ hψ ψ' hψ' Q hfac
  have hmass := (pairQuotientMeasure_isCompatible K hK ψ ψ').compactOpenQuotientOrbit_mass
    (targetCompactOpen (radical ψ') Q) (targetCompactOpen_isCompact (radical ψ') hU₁ Q hQc)
  let e := compactTestVector h₀ hU₀ hP₀ K hK hr₀ ν hν A hδ₀ hψK hQc hQK hv
  let c : ℂ := ((μquot (sourceTestOrbit (radical ψ) (radical ψ') Q)).toReal : ℂ)
  refine ⟨e, c, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hmass.1.ne' hmass.2.ne).ne', ?_⟩
  intro z
  refine continuedOperator_map_eq_of_eqOn (parameterScheme χ)
    (DynamicOppositeCanonicalScalar.parameterProjection_continuous χ)
    (parameterScheme_isConnectedReductive χ hG) p.presentation p.isOpen_region p.nonempty_region
    (fun _ hz => hz) (compactPictureEvalOne h₁ K A) e (c • v) ?_ z
  intro x hx
  let w : pairFullDomainRegion χ K hK ψ hψ ψ' A := ⟨x, p.converges hx⟩
  change compactPictureEvalOne h₁ K A
    (compactFamily χ hG K hK ψ hψ hψK ψ' hψ' hψ'K p.modulus A w e) = c • v
  exact compactIntertwiningOperator_compactTestVector_eval_one h₀ hU₀ hP₀ K hK hr₀ ν hν A hδ₀ hψK
    h₁ hU₁ hδ₁ hP₁ hψ'K hr₁ μquot (levi_isClosed χ) hQc hQK hv hloc hmass.2.ne
    (parameterTransport χ w.val) (pairFamily χ K hK ψ hψ ψ' hψ' p.modulus A w)
    (pairFamily_spec χ K hK ψ hψ ψ' hψ' p.modulus A w)

/-- Choose a fixed compact section for the given vector with its uniform
continued identity evaluation. -/
def continuedPairCompactTest (v : A) :
    {e : CompactInductionPicture h₀ K A // ∃ c : ℂ, c ≠ 0 ∧ ∀ z : p.regularRegion,
      compactPictureEvalOne h₁ K A (p.presentation.continuedOperator z e) = c • v} :=
  ⟨Classical.choose (exists_continuedPair_eval_one_eq χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p v),
    Classical.choose_spec (exists_continuedPair_eval_one_eq χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p v)⟩

/-- The whole compact continued map is nonzero at every regular parameter
for a nonzero inducing carrier. -/
theorem continuedPair_continuedOperator_ne_zero [Nontrivial A] (z : p.regularRegion) :
    p.presentation.continuedOperator z ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  let e := continuedPairCompactTest χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p v
  obtain ⟨c, hc, he⟩ := e.property
  intro hz
  have h := he z
  rw [hz, LinearMap.zero_apply, map_zero] at h
  exact (smul_ne_zero hc hv) h.symm

/-- The same nonvanishing holds for the actual ambient intertwiner. -/
theorem continuedPair_operator_ne_zero [Nontrivial A] (z : p.regularRegion) :
    ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z ≠ 0 := by
  intro hz
  apply continuedPair_continuedOperator_ne_zero χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z
  have h := ContinuedPair.operator_compact χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z
  rw [hz] at h
  exact h.symm.trans (LinearMap.ext fun _ => by simp only [LinearMap.comp_apply,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply, map_zero])

/-- On irreducible fibers the actual continued map is bijective by its
compact-test nonvanishing. The fiber hypotheses can be used on a generic
subregion. -/
theorem continuedPair_operator_bijective_of_irreducible [Nontrivial A] (z : p.regularRegion)
    (hsrc : (UnramifiedLeviInduction h₀ hU₀ ν (parameterTransport χ z.val) A).representation.IsIrreducible)
    (htgt : (UnramifiedLeviInduction h₁ hU₁ ν (parameterTransport χ z.val) A).representation.IsIrreducible) :
    Function.Bijective (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z) := by
  let := hsrc
  let := htgt
  exact (Representation.IsIrreducible.bijective_or_eq_zero
    (ContinuedPair.operator χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z)).resolve_right
      (continuedPair_operator_ne_zero χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p z)

end Langlands.Plancherel.ActualCommonLeviTensor
