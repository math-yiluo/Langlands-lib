import Langlands.Representation.Plancherel.ActualTranslatedCompactTensor

/-! # The chart of the translated V.3 tensor -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 260000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualTranslatedCompactTensor

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open ActualConjugateLeviTwist ActualConjugateLeviRationalParameter UnramifiedOperatorFamily

private theorem composeCompactCharts
    {H V W Y Vc Wc Yc : Type*} [Monoid H]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Vc] [Module ℂ Vc]
    [AddCommGroup Wc] [Module ℂ Wc] [AddCommGroup Yc] [Module ℂ Yc]
    {ρ : Representation ℂ H W} {σ : Representation ℂ H Y}
    (source : V ≃ₗ[ℂ] Vc) (middle : W ≃ₗ[ℂ] Wc) (target : Y ≃ₗ[ℂ] Yc)
    (translation : V →ₗ[ℂ] W) (standard : ρ.IntertwiningMap σ)
    (compactTranslation : Vc →ₗ[ℂ] Wc) (compactStandard : Wc →ₗ[ℂ] Yc)
    (ambient : V →ₗ[ℂ] Y) (chart result : Vc →ₗ[ℂ] Yc)
    (htranslation : compactTranslation =
      middle.toLinearMap.comp (translation.comp source.symm.toLinearMap))
    (hambient : ambient = standard.toLinearMap.comp translation)
    (hchart : chart = target.toLinearMap.comp (ambient.comp source.symm.toLinearMap))
    (hresult : result = compactStandard.comp compactTranslation)
    (hstandard : ∀ v, target (standard v) = compactStandard (middle v)) :
    result = chart := by
  rw [hresult, hchart, hambient, htranslation]
  apply LinearMap.ext
  intro v
  exact (hstandard (translation (source.symm v))).symm

private theorem composeNumerator_clears
    {V W Y : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
    {numerator standard : W →ₗ[ℂ] Y} {translation : V →ₗ[ℂ] W}
    {chart : V →ₗ[ℂ] Y} {b : ℂ}
    (hnumerator : numerator = b • standard) (hchart : standard.comp translation = chart) :
    numerator.comp translation = b • chart := by
  rw [hnumerator, LinearMap.smul_comp, hchart]

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
  (hG : IsConnectedReductive G) (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ x : RationalPoint F G.X, ∃ p : parabolic χ, ∃ k : K,
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

set_option hygiene false in
set_option quotPrecheck false in
local notation "χg" => (χ ≫ (G.innerIso g).hom)
set_option hygiene false in
local notation "Ag" => conjugateRepresentation χ g A
set_option hygiene false in
local notation "X" => unramifiedCharacters (normCharacters χ)

variable (K' : OpenSubgroup (RationalPoint F G.X))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))
  (hχgK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic χg, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))

set_option hygiene false in
local notation "C₀" => compactTensorEquiv χ hG K hK χ rfl hPK A
set_option hygiene false in
local notation "L" => ActualConjugateLeviTensor.translatedCoefficient χ g hG A K hK hPK

variable (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χg)
  (hψK' : ∀ x : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K',
    x = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag)
  (q : ContinuedPair χg hG K' hK' ψ hψ hψK' χg rfl hχgK' (Ag).contragredient)

set_option hygiene false in
local notation "D" => ActualConjugateLeviTensor.genericLocus χ g hG A K' hK' hχgK' ψ hψ hψK' p q

set_option hygiene false in
local notation "Cg" => compactTensorEquiv χg hG K' hK' χg rfl hχgK' Ag
set_option hygiene false in
local notation "Ct" => compactTensorEquiv χg hG K' hK' ψ hψ hψK' Ag
set_option hygiene false in
local notation "Sc" => ActualCommonLeviCompactTensor.compactComparison
  χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag p q
set_option hygiene false in
local notation "S" => ActualCommonLeviTensor.genericComparison
  χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag p q
set_option hygiene false in
local notation "Cc" => compactComparison χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "Vc" => ActualConjugateLeviV3.compactComparison
  χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "w" => (ActualConjugateLeviTensor.genericParameter χ g hG A
  K' hK' hχgK' ψ hψ hψK' p q z)
set_option hygiene false in
local notation "Lc" => compactTranslation χ g hG A K hK hPK K' hK' hχgK'
set_option hygiene false in
local notation "Jc" => pulledBackStandardTensor χ g hG A K' hK' hχgK' ψ hψ hψK' p q
set_option hygiene false in
local notation "J" => ActualConjugateLeviTensor.genericComparison χ g hG A K hK hPK
  K' hK' hχgK' ψ hψ hψK' p q

private theorem compact_composite_map (z : D) :
    Cc z = (Sc w).comp (Lc z.val) := by
  delta ActualTranslatedCompactTensor.compactComparison pulledBackStandardTensor
  with_reducible rfl

set_option maxHeartbeats 500000 in
private theorem translation_map_eq (z : X) :
    Lc z = (Cg (conjugateParameter χ g z)).toLinearMap.comp
      ((L z).toIntertwiningMap.toLinearMap.comp (C₀ z).symm.toLinearMap) := by
  delta compactTranslation
  with_reducible rfl

private theorem ambient_chart_map (z : D) :
    Vc z = (Ct (conjugateParameter χ g z.val)).toLinearMap.comp
      ((J z).toLinearMap.comp (C₀ z.val).symm.toLinearMap) := by
  delta ActualConjugateLeviV3.compactComparison
  with_reducible rfl

set_option maxHeartbeats 700000 in
set_option allowUnsafeReducibility true in
attribute [local reducible] ActualConjugateLeviTensor.genericLocus
  ActualConjugateLeviTensor.genericParameter Set.preimage
  Set.restrictPreimage Set.MapsTo.restrict Subtype.map in
private theorem standard_chart_apply (z : D)
    (v : coefficientFiber χg χg rfl Ag (conjugateParameter χ g z.val)) :
    Ct (conjugateParameter χ g z.val) (S w v) =
      Sc w (Cg (conjugateParameter χ g z.val) v) := by
  exact ActualCommonLeviCompactTensor.compactComparison_square
    χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag p q w v

set_option maxHeartbeats 600000 in
set_option allowUnsafeReducibility true in
attribute [local reducible] ActualConjugateLeviTensor.genericLocus
  ActualConjugateLeviTensor.genericParameter Set.preimage
  Set.restrictPreimage Set.MapsTo.restrict Subtype.map in
private theorem ambient_composite_map (z : D) :
    (J z).toLinearMap = (S w).toLinearMap.comp (L z.val).toIntertwiningMap.toLinearMap := by
  delta ActualConjugateLeviTensor.genericComparison
  simp only [Representation.IntertwiningMap.comp_toLinearMap]

set_option maxHeartbeats 700000 in
private theorem chart_pointwise (z : D) : Cc z = Vc z := by
  exact composeCompactCharts
    (C₀ z.val) (Cg (conjugateParameter χ g z.val)) (Ct (conjugateParameter χ g z.val))
    (L z.val).toIntertwiningMap.toLinearMap (S w) (Lc z.val)
    (Sc w) (J z).toLinearMap (Vc z) (Cc z)
    (translation_map_eq χ g hG A K hK hPK K' hK' hχgK' z.val)
    (ambient_composite_map χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q z)
    (ambient_chart_map χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q z)
    (compact_composite_map χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q z)
    (standard_chart_apply χ g hG A K' hK' hχgK' ψ hψ hψK' p q z)

/-- The translation and actual compact standard tensor realize the ambient
comparison in the V.3 chart on the simultaneous generic locus. -/
theorem agreesWithV3CompactChart :
    AgreesWithV3CompactChart χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q :=
  chart_pointwise χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q

private theorem compact_pulledBack_composite_map (z : D) :
    Cc z = (Jc z).comp (Lc z.val) := by
  delta ActualTranslatedCompactTensor.compactComparison
  with_reducible rfl

set_option maxHeartbeats 500000 in
private theorem compactChartNumerator_clears (standard : RationalOperatorContinuationData D Jc)
    (z : D) :
    (standard.numerator z.val).comp (Lc z.val) = standard.denominator.val z.val • Vc z :=
  composeNumerator_clears (standard.clears z)
    ((compact_pulledBack_composite_map χ g hG A K hK hPK
      K' hK' hχgK' ψ hψ hψK' p q z).symm.trans
      (chart_pointwise χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q z))

/-- Compose the global numerator of the actual pulled-back standard tensor
with the polynomial compact translation and keep its denominator. -/
def compactChartContinuation (standard : RationalOperatorContinuationData D Jc)
    (hL : IsPolynomialOperatorOn Set.univ (fun z => Lc z.val)) :
    RationalOperatorContinuationData D Vc where
  denominator := standard.denominator
  denominator_nonzero := standard.denominator_nonzero
  numerator z := (standard.numerator z).comp (Lc z)
  polynomial := standard.polynomial.comp hL
  clears := compactChartNumerator_clears χ g hG A K hK hPK
    K' hK' hχgK' ψ hψ hψK' p q standard

/-- The actual reverse-dual scalar data and polynomiality on the generic
locus also suffice for a whole-operator denominator in the V.3 chart. -/
theorem compactChart_rational_of_polynomialTranslation
    (d : ScalarInverseData χg hG K' hK' χg rfl hχgK' ψ hψ hψK' Ag p q)
    (hL : IsPolynomialOperatorOn D (fun z => Lc z.val)) :
    IsRationalOperatorOn D Vc := by
  have h : Cc = Vc :=
    funext (chart_pointwise χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q)
  rw [← h]
  exact compactComparison_rational_of_polynomialTranslation
    χ g hG A K hK hPK K' hK' hχgK' ψ hψ hψK' p q d hL

end Langlands.Plancherel.ActualTranslatedCompactTensor
