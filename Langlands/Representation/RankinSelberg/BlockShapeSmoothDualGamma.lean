import Langlands.Representation.RankinSelberg.BlockShapeCenteredGamma
import Langlands.Representation.Parabolic.NaturalInductionDualityProof
import Langlands.Representation.Tensor.SmoothDualInjectivityProof
import Langlands.Representation.Tensor.SmoothDualSurjectivityProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-! # Whole smooth-dual gamma factors on actual block shapes -/

noncomputable section

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Smooth duality for the actual normalized product, retaining the same
upper block parabolic and the actual smooth dual of every supplied block. -/
def HasNormalizedProductSmoothDualEquivalence {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) : Prop :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  Nonempty ((smoothContragredient (T.normalizedProductInduced B π)).Equiv
    (T.normalizedProductInduced B (fun i => smoothContragredient (π i))))

/-- Natural normalized induction duality and finite tensor duality identify
the whole smooth dual with the normalized product of the block smooth duals. -/
theorem hasNormalizedProductSmoothDualEquivalence {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (ha : letI := T.topology; ∀ i, IsAdmissible (π i)) :
    HasNormalizedProductSmoothDualEquivalence T B π := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
  let := T.leviTopologicalGroup B
  let σ : Rep.{uV} ℂ (B.Levi F.Carrier) := Rep.of (B.blockTensor π)
  have hσ : IsAdmissible σ.ρ := FiniteTensor.isAdmissible_external π ha
  obtain ⟨EI, -⟩ := Parabolic.naturalNormalizedInductionDuality.{uF, uV}.1 p F T n B
  have hbij : Function.Bijective (FiniteTensor.smoothDualTensorMap π) :=
    ⟨FiniteTensor.smoothDualTensorInjectivity.{0, uF, uV} (Fin B.length) _ _ π,
      FiniteTensor.smoothDualTensorMap_surjective π ha
        (fun i => GeneralLinear.compactOpen_cofinal F T (B.size i))⟩
  let e : (FiniteTensor.external (fun i => smoothContragredient (π i))).Equiv
      (smoothContragredient (FiniteTensor.external π)) :=
    Representation.Equiv.mk (LinearEquiv.ofBijective _ hbij)
      (FiniteTensor.smoothDualTensorIntertwiner π).isIntertwining'
  exact ⟨(EI σ hσ).trans (T.normalizedParabolicInducedEquiv B e.symm)⟩

/-- Choose the actual whole-dual/product-of-duals equivalence. -/
def normalizedProductSmoothDualEquiv {n : ℕ} (B : BlockShape n)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (ha : letI := T.topology; ∀ i, IsAdmissible (π i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    letI (i : Fin B.length) := T.generalLinearTopologicalGroup (B.size i)
    (smoothContragredient (T.normalizedProductInduced B π)).Equiv
      (T.normalizedProductInduced B (fun i => smoothContragredient (π i))) :=
  (hasNormalizedProductSmoothDualEquivalence T B π ha).some

end Langlands.PadicField.TopologicalData

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker Classification LocalFactor

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- A gamma certificate on the original action and its whole smooth dual
transports to the corresponding product and the product of actual block duals. -/
theorem IsPadicSymmetricGammaFactor.normalizedProduct_smoothDual {r : ℕ}
    (B : BlockShape (r + 1))
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (ha : ∀ i, IsAdmissible (π i))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (e : ρ.Equiv (F.canonicalTopologicalData.normalizedProductInduced B π))
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val ρ (smoothContragredient ρ) G) :
    IsPadicSymmetricGammaFactor F ψ ν.val
      (F.canonicalTopologicalData.normalizedProductInduced B π)
      (F.canonicalTopologicalData.normalizedProductInduced B
        (fun i => smoothContragredient (π i))) G :=
  (IsPadicSymmetricGammaFactor.congr_equiv e
    ((smoothContragredientEquiv e).symm.trans
      (F.canonicalTopologicalData.normalizedProductSmoothDualEquiv B π ha))).mp hG

/-- The centered gamma germ can be read from a certificate on the original
action and its actual whole smooth dual. -/
theorem centeredSegmentFamilyGammaGerm_of_smoothDualGamma
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {r : ℕ} (B : BlockShape (r + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hirr : ∀ i, (δ i).IsIrreducible) (hadm : ∀ i, (δ i).IsAdmissible)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (e : ρ.Equiv (F.canonicalTopologicalData.twistedProductInduced B δ s).representation)
    (hf : HasFunctional (N := upperUnipotent (r + 1) F.Carrier)
      (θ := standardCharacter ψ r) ρ)
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val ρ (smoothContragredient ρ) G) :
    ∃ (c : ℂˣ) (m : ℤ), IsCenteredSegmentFamilyGammaGerm F d s G
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal)
      (epsilonMonomial F.canonicalTopologicalData.residueCardinality c m) := by
  have ha (i) : IsAdmissible
      (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).representation :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter
        (B.size i) (s i))).mpr (hadm i)
  have hmix := hG.normalizedProduct_smoothDual F ψ ν B
    (fun i => (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).representation)
    ha ρ e
  exact centeredSegmentFamilyGammaGerm_of_blockShape F ψ ν hH hEq B δ s d hirr hadm
    ((hasFunctional_iff_of_equiv e).mp hf) hmix

/-- Whole smooth-dual gamma data and the real-order restriction imply the
unitary supercuspidal product conclusion for the original supplied action. -/
theorem unitarySupercuspidalProduct_of_smoothDualGamma
    (hH : SegmentHeadLFactorStatement.{uF, max uF uV, max uF uV})
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {r : ℕ} (B : BlockShape (r + 1))
    (δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hU : IsUnitaryGenericDatum F F.canonicalTopologicalData B δ s)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (e : ρ.Equiv (F.canonicalTopologicalData.twistedProductInduced B δ s).representation)
    (hf : HasFunctional (N := upperUnipotent (r + 1) F.Carrier)
      (θ := standardCharacter ψ r) ρ)
    {G : RatFunc ℂ}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val ρ (smoothContragredient ρ) G)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0) :
    IsUnitarySupercuspidalProduct.{uF, uW, uX} F F.canonicalTopologicalData B ρ := by
  have ha (i) : IsAdmissible
      (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).representation :=
    (Langlands.isAdmissible_twist_iff _ _
      (F.canonicalTopologicalData.isOpen_ker_determinantPowerCharacter
        (B.size i) (s i))).mpr (hU.1 i).2.2.isAdmissible
  have hmix := hG.normalizedProduct_smoothDual F ψ ν B
    (fun i => (F.canonicalTopologicalData.segmentFactor (δ i) (s i)).representation)
    ha ρ e
  exact unitarySupercuspidalProduct_of_blockShapeGamma
    F ψ ν hH hEq B δ s d hU ρ e hf hmix hzero

end Langlands.RankinSelberg
