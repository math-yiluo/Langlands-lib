import Langlands.Representation.RankinSelberg.CenteredSegmentFamilyGamma
import Langlands.Representation.Classification.SupercuspidalInductionTransports
import Langlands.Representation.Classification.SupercuspidalProductRealization

/-! # From centered segment rigidity to actual supercuspidal products -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The supplied action is equivalent to the whole normalized product of
unitarizable supercuspidal blocks of the specified shape, with block carriers
in the independently prescribed universe. -/
def IsUnitarySupercuspidalProduct {n : ℕ} (B : BlockShape n)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) : Prop :=
  letI := T.topology
  ∃ σ : ∀ i, SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := B.size i),
    (∀ i, IsUnitarizable (σ i).obj.representation) ∧
      Nonempty (ρ.Equiv (T.normalizedProductInduced B
        (fun i => (σ i).obj.representation)))

private theorem supercuspidal_of_rank_transport {m n : ℕ} (h : m = n)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology
      (h.symm ▸ π).IsIrreducible ∧
        IsSupercuspidal (h.symm ▸ π).representation) :
    letI := T.topology
    π.IsIrreducible ∧ IsSupercuspidal π.representation := by
  cases h
  exact hπ

/-- A one-term parameter makes the original supplied square-integrable block
supercuspidal, after eliminating its exact degree equality. -/
theorem SquareIntegrableSegmentParameter.supercuspidal_of_length_one
    {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (d : SquareIntegrableSegmentParameter F T n π)
    (h1 : d.segment.length = 1) :
    letI := T.topology
    π.IsIrreducible ∧ IsSupercuspidal π.representation := by
  exact supercuspidal_of_rank_transport F T d.degree_eq π
    (d.head.isSegmentQuotient.supercuspidal_of_length_one T h1)

/-- One-term segments and zero exponents turn an equivalence to the whole
twisted product into a unitary supercuspidal product of the same shape.
The source action and the output block universe remain independent. -/
theorem unitarySupercuspidalProduct_of_length_one_zero_exponents
    {n : ℕ} (B : BlockShape n)
    (δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (s : Fin B.length → ℝ)
    (d : ∀ i, SquareIntegrableSegmentParameter F T (B.size i) (δ i))
    (hδ : letI := T.topology; ∀ i, IsUnitarizable (δ i).representation)
    (h1 : ∀ i, (d i).segment.length = 1) (hs : ∀ i, s i = 0)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (e : letI := T.topology; ρ.Equiv (T.twistedProductInduced B δ s).representation) :
    IsUnitarySupercuspidalProduct.{uF, uW, uX} F T B ρ := by
  let := T.topology
  let A : ∀ i, SupercuspidalRep.{uF, max uF uV}
      (F := F.Carrier) (n := B.size i) :=
    fun i => ⟨δ i, (d i).supercuspidal_of_length_one F T (h1 i)⟩
  have e0 : ρ.Equiv
      (T.normalizedProductInduced B (fun i => (A i).obj.representation)) :=
    e.trans (SmoothRep.equivOfIso (T.twistedProductInducedZeroIso B δ s hs))
  exact T.exists_unitary_supercuspidal_product_equiv B A hδ ρ e0

end Langlands.Classification

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis Polynomial Classification LocalFactor

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance centeredProductTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Actual gamma rigidity produces an equivalence of the original action
with the whole unitary supercuspidal product, in any output block universe.
All analytic factor identities and the order restriction remain premises. -/
theorem centeredSegmentFamily_unitarySupercuspidalProduct_of_unitaryGenericDatum
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    {N : ℕ} {B : BlockShape N} [Nonempty (Fin B.length)]
    {δ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {s : Fin B.length → ℝ}
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i))
    (hU : IsUnitaryGenericDatum F F.canonicalTopologicalData B δ s)
    {P Pd : ℂ[X]}
    (hL : IsCenteredSegmentFamilyLProductPair F d s P Pd
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal))
    (c : ℂˣ) (m : ℤ) {G : RatFunc ℂ}
    (hG : G = rationalGammaExpression (residueReflection F) c m P Pd)
    (hPd : Pd ≠ 0)
    (hzero : ∀ t : ℝ, 0 < meromorphicOrderAt
      (rationalSpectralValue F.canonicalTopologicalData.residueCardinality G) (t : ℂ) →
      t = 0)
    {V : Type uX} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear N F.Carrier) V)
    (e : ρ.Equiv (F.canonicalTopologicalData.twistedProductInduced B δ s).representation) :
    IsUnitarySupercuspidalProduct.{uF, uW, uX} F F.canonicalTopologicalData B ρ := by
  have hr := centeredSegmentFamily_rigidity_of_unitaryGenericDatum
    F ψ ν hEq d hU hL c m hG hPd hzero
  exact unitarySupercuspidalProduct_of_length_one_zero_exponents
    F F.canonicalTopologicalData B δ s d (fun i => (hU.1 i).2.1)
    (fun i => (hr i).1) (fun i => (hr i).2) ρ e

end Langlands.RankinSelberg
