import Langlands.Representation.Classification.BernsteinOrderZeroPositivity
import Langlands.Representation.Exponents.DescendingIntervalBlockScalarProof
import Langlands.Representation.Exponents.SquareIntegrableInductionEmbeddingConeProof

/-! # Square-integrable subrepresentations of unitary block products -/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands

universe uF uV

/-- A normalized block product of irreducible unitarizable factors can contain
a nonzero square-integrable subrepresentation only when there is one block. -/
def SquareIntegrableUnitaryProductStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : GeneralLinear.BlockShape n)
      (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
      (∀ i, (σ i).representation.IsIrreducible ∧ IsUnitarizable (σ i).representation) →
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) [Nontrivial π],
        T.IsSquareIntegrable π.representation →
        SmoothRep.IsSubrepresentation π ((T.normalizedProductInductionFunctor B).obj σ) →
        B.length = 1

/-- The unitary block characters have real part zero, which the strict
Jacquet-exponent condition permits only for the one-block shape. -/
theorem squareIntegrableUnitaryProduct : SquareIntegrableUnitaryProductStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn B σ hσ π _ hπ hsub
  choose ω hω hnorm using fun i =>
    Classification.exists_hasScalarCharacter_norm_one_of_isUnitarizable F T
      (σ i) (hσ i).1 (hσ i).2
  let χ : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
    ∏ i, (ω i).comp (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
  have hχ : T.IsRealPartOf χ (fun _ => 0) := by
    intro a
    simp only [χ, MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod,
      MonoidHom.comp_apply, Pi.evalMonoidHom_apply, hnorm, Finset.prod_const_one, Real.rpow_zero]
  let τ := FiniteTensor.externalSmoothObject σ
  have hscalar := B.hasScalarCharacter_blockTensor_splitCentre F.Carrier hω
  have hcone := squareIntegrableInductionEmbeddingCone.{uF, uV} p F T n hn π hπ B τ hsub
    χ hscalar (fun _ => 0) hχ
  have hlength : B.length ≤ 1 := by
    by_contra! h
    simpa [Exponents.partialSum] using hcone.2 1 Nat.zero_lt_one h
  have hnonzero : B.length ≠ 0 := by
    intro h
    have : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
    have hn' := B.sum_eq
    rw [Finset.sum_of_isEmpty] at hn'
    omega
  omega

end Langlands
