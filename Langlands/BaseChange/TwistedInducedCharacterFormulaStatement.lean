import Langlands.BaseChange.InducedCharacterFormulaStatement
import Langlands.BaseChange.TwistedCharacter.Basic

/-! # The twisted induced character formula at σ-regular points

This module states the twisted case of Henniart–Lemaire (2011), II.4.5, formula (3). It
supplies no proof.
-/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear JacquetLanglands

universe u v uW

/-- Twisted Henniart–Lemaire II.4.5 (3). Let `δ ∈ GL_n(E)` be norm associated with a regular
semisimple `γ ∈ GL_n(F)`, let `m` be a Levi class system for `γ`, and let each `d j` be a
σ-conjugate of `δ` in the Levi `M(E)` whose blocks have exact cyclic norms the blocks of
`m j`. Then the twisted character of the normalized product induction of irreducible
admissible σ-stable block representations, for `ι(A)`, is the sum of
`|D_{G/M}(m_j)|_F^{-1/2}` times the twisted character value of the Levi tensor
representation at `d j` for `A₁ ⊗ ⋯ ⊗ A_r`. An empty system gives the value zero. -/
def TwistedInducedCharacterFormulaStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l → 0 < n → ∀ (B : BlockShape n)
    (W : Fin B.length → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (P : ∀ i, Representation ℂ (GeneralLinear (B.size i) E) (W i))
    (hP : ∀ i, IsAdmissible (P i)) (A : ∀ i, SigmaIntertwiner σ (B.size i) (P i)),
    (∀ i, (P i).IsIrreducible) →
    ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
    ∀ (k : ℕ) (m : Fin k → B.Levi F), IsLeviClassSystem B γ m →
    ∀ (d : Fin k → B.Levi E),
      (∀ j, (∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = B.leviEmbedding E (d j)) ∧
        ∀ i, cyclicNorm σ l (d j i) = baseChange F E (B.size i) (m j i)) →
    ∀ (b : Fin k → ℂ),
      (∀ j,
        haveI : ∀ i, T2Space (GeneralLinear (B.size i) E) := fun i =>
          LocalFieldTopology.generalLinear_t2Space E (B.size i)
        haveI : ∀ i, LocallyCompactSpace (GeneralLinear (B.size i) E) := fun i =>
          LocalFieldTopology.generalLinear_locallyCompactSpace E (B.size i)
        haveI : ∀ i, TotallyDisconnectedSpace (GeneralLinear (B.size i) E) := fun i =>
          LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (B.size i)
        HasTwistedCharacterValue (B.blockTensor P) (FiniteTensor.isAdmissible_external P hP)
          (leviTensorIntertwiner σ B A).toLinearMap (d j) (b j)) →
      haveI := LocalFieldTopology.generalLinear_t2Space E n
      haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
      haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
      HasTwistedCharacterValue ((LocalFieldData.ofInstances E).normalizedProductInduced B P)
        (isAdmissible_normalizedProductInduced B P hP) (inducedSigmaIntertwiner σ B A).toLinearMap
        δ (∑ j, relativeDiscriminantWeight B (m j) * b j)

end Langlands.BaseChange
