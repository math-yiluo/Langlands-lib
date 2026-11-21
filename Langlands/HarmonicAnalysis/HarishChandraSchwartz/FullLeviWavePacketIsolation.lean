import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviWavePacketIntegral
import Langlands.Representation.Plancherel.SmoothOrbitSectionFiniteValues
import Langlands.Representation.Plancherel.CoefficientTensorInjectivity

/-! # Finite isolation of an ambient coefficient in the full-Levi packet -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν Finset.univ
set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "A" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hA" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "B" => rationalLeviSplitCenter Finset.univ sL
set_option hygiene false in
local notation "hB" => rationalLeviSplitCenter_le_center Finset.univ sL hsL
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν

variable [(A).Normal] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "muM" => rationalFullLeviQuotientHaar hG hi hν s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
  (hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu)

set_option hygiene false in
local notation "πM" => IrreducibleAdmissibleRep.pullback eG π
set_option hygiene false in
local notation "ω" => discreteSeriesClass A hA mu π hsq

set_option hygiene false in
local notation "hsqM" => rationalFullLeviPullback_isSquareIntegrable hG hi hν s hs mu π hsq
set_option hygiene false in
local notation "ωM" => discreteSeriesClass B hB muM πM hsqM
set_option hygiene false in
local notation "eO" => rationalFullLeviOrbitHomeomorph hG hi hν s hs mu ω

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "sections" =>
  rationalInducedSmoothOrbitSections hG hi hν Finset.univ hKc hPK πM
set_option hygiene false in
local notation "coeff" =>
  rationalInducedOrbitCoefficientMap hG hi hν Finset.univ hKc hPK πM B hB muM hsqM

set_option hygiene false in
local notation "OM" => discreteSeriesOrbit B hB muM νM ωM
set_option hygiene false in
local notation "OG" => discreteSeriesOrbit A hA mu νG ω
set_option hygiene false in
local notation "tensor" => rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK

set_option hygiene false in
local notation "e" => rationalFullLeviInducingOrbitHomeomorph hG hi hν s hs mu π hsq
set_option hygiene false in
local notation "x₀" => discreteSeriesOrbitMap A hA mu νG ω 1
set_option hygiene false in
local notation "Rmap" => unitaryOrbitRepresentativeDiscreteSeriesOrbit νM πM B hB muM hsqM

omit [IsAffine T.X.left] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [(A).Normal] [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)] [mu.IsHaarMeasure] in
/-- The unaltered inducing representative belongs to its own unitary twist
orbit via the trivial character. -/
def rationalFullLeviBaseRepresentative : UnitaryOrbitRepresentative νM πM := by
  refine ⟨πM, 1, ?_⟩
  let C : SmoothDualClass.{0, u, uV} (k := ℂ) (G := 𝐌) := Quotient.mk _ πM
  change (1 : unramifiedCharacters νM) • C = C
  exact one_smul _ _

set_option hygiene false in
local notation "R₀" => rationalFullLeviBaseRepresentative hG hi hν π

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
private theorem fullLeviOrbit_homeomorph_base : Rmap R₀ = e x₀ := by
  have he : e x₀ = (eO) x₀ := by
    unfold rationalFullLeviInducingOrbitHomeomorph
    rfl
  refine Eq.trans ?_ he.symm
  apply Subtype.ext
  have h₀ : (x₀).val = ω := one_smul _ _
  have h := rationalFullLeviOrbitHomeomorph_val hG hi hν s hs mu ω x₀
  exact (congrArg (rationalFullLeviDiscreteSeriesClass hG hi hν s hs mu) h₀.symm).trans h.symm

set_option maxHeartbeats 300000 in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
private theorem fullLeviOrbit_coefficient_representative
    (q : sections) (x : OG) (R : UnitaryOrbitRepresentative νM πM) (hR : Rmap R = e x) :
    coefficientTensorMap (Quotient.out x.val.val).obj (tensor q x) =
      rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK R.val.obj R.val.property.2
        (q.val R) := by
  have hrep := rationalInducedOrbitCoefficientMap_representative
    hG hi hν Finset.univ hKc hPK πM B hB muM hsqM q R
  have he : e x = (eO) x := by
    unfold rationalFullLeviInducingOrbitHomeomorph
    rfl
  have hx := congrArg (fun (y : OM) => coeff q y) (hR.trans he)
  have ht := coefficientTensorMap_rationalFullLeviOrbitCoefficientTensor
    hG hi hν s hs mu π hsq hKc hPK q x
  unfold rationalFullLeviAmbientOrbitCoefficient at ht
  with_reducible_and_instances exact ht.trans (hx.symm.trans hrep)

set_option hygiene false in
local notation "FΦ" => productInducedCoefficientObject
  (isSemidirectDecomposition_standard hG hi hν
    (RationalPointFamily.rootSet_subset i ν Finset.univ))
  (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)) (πM).obj

set_option hygiene false in
local notation "hindexM" => finiteIndex_splitValuationImage_of_isSplitComponent
  (isConnectedReductive_leviScheme_rootSet hG hi hν Finset.univ) sL hsL

set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any product-induced value can be prescribed at the base representative
while the ambient tensors vanish at a finite set of other orbit points. -/
theorem exists_rationalFullLeviOrbitCoefficientTensor_finiteIsolation
    (Φ : FΦ) (X : Set OG) (hX : X.Finite) (hx₀ : x₀ ∉ X) :
    ∃ q : sections,
      coefficientTensorMap (Quotient.out (x₀).val.val).obj (tensor q x₀) =
        rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK (πM).obj (πM).property.2 Φ ∧
      ∀ x ∈ X, tensor q x = 0 := by
  let := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν Finset.univ
  let := finite_standardLeviDiscreteSeriesStabilizer Finset.univ sL hsL hindexM muM ωM
  let : Finite (unitaryClassTwistStabilizer νM (Quotient.mk _ πM)) :=
    Finite.of_injective _ (unitaryClassStabilizerEquivDiscreteSeries νM πM B hB muM hsqM).injective
  obtain ⟨rep, hrep⟩ :=
    (unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective νM πM B hB muM hsqM).hasRightInverse
  let r : OG → UnitaryOrbitRepresentative νM πM := fun x => rep (e x)
  have hr (x : OG) : Rmap (r x) = e x := hrep (e x)
  have hb := fullLeviOrbit_homeomorph_base hG hi hν s hs mu π hsq
  have hclasses : ∀ R ∈ r '' X,
      (Quotient.mk _ R.val : SmoothDualClass.{0, u, uV} (k := ℂ) (G := 𝐌)) ≠
        Quotient.mk _ (R₀).val := by
    rintro _ ⟨x, hx, rfl⟩ h
    have heq : Rmap (r x) = Rmap R₀ := Subtype.ext (Subtype.ext h)
    exact hx₀ ((e).injective ((hr x).symm.trans (heq.trans hb)) ▸ hx)
  obtain ⟨q, hq₀, hqX⟩ := exists_productInducedSmoothOrbitSection_finiteClasses
    νM πM (leviRationalUnitaryCoordinates hG hi hν Finset.univ).toMulEquiv
    (isSemidirectDecomposition_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ))
    (isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)) K
    (isClosed_standardParabolicPoints_rootSet hG hi hν Finset.univ) hKc
    (RationalPointFamily.continuous_leviRationalNormCharacters i ν Finset.univ)
    (continuous_projection_standard hG hi hν
      (RationalPointFamily.rootSet_subset i ν Finset.univ) _)
    (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν _ hPK))
    R₀ (r '' X) (hX.image r) hclasses Φ
  refine ⟨q, ?_, ?_⟩
  · have h := fullLeviOrbit_coefficient_representative hG hi hν s hs mu π hsq hKc hPK q x₀ R₀ hb
    have hv : q.val R₀ = Φ := hq₀
    refine h.trans (DFunLike.congr ?_ hv)
    unfold rationalFullLeviBaseRepresentative
    rfl
  · intro x hx
    let Q := Quotient.out x.val.val
    apply coefficientTensorMap_injective Q.obj Q.property.2 Q.property.1
    have h := fullLeviOrbit_coefficient_representative hG hi hν s hs mu π hsq hKc hPK
      q x (r x) (hr x)
    have hv : q.val (r x) = 0 := hqX (r x) ⟨x, hx, rfl⟩
    exact h.trans ((congrArg (rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK
      (r x).val.obj (r x).val.property.2) hv).trans ((map_zero _).trans (map_zero _).symm))

end Langlands.HarishChandraSchwartz
