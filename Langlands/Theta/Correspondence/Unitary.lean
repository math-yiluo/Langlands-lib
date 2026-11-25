import Langlands.Theta.Correspondence.ThetaLift
import Langlands.Theta.DualPair.Unitary.Pair

/-!
# Howe duality for the unitary dual pairs with `W` split: the statement

GKT Theorem 13.21 (Howe duality, p. 401) for the Weil representation `ω_{ψ,s} = ω_ψ ∘ s`
(Definition 13.15, p. 399) of the unitary dual pair `(U(ν, ν), U(Q))` (Case `3₊` with `W` split)
and its Leray splitting with data `(χ, ψ)` and `μ = 1` (`pairSplitting`,
`Langlands.Theta.DualPair.Unitary.Pair`). The statement is a `Prop`; it is not proved here.
-/

noncomputable section

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

/-- **Howe duality for the unitary dual pairs `(U(ν, ν), U(Q))`** (GKT Theorem 13.21, Case `3₊`
with `W` split): for every quadratic extension `E / F` of nonarchimedean local fields of
characteristic zero, every invertible Hermitian `Q`, every character `χ` of `Eˣ` with
`χ|_{Fˣ} = χ_{E/F}^{|α|}` and every non-trivial `ψ`, the Weil representation `pairWeil` of the
Leray splitting of the pair satisfies `HoweDuality` (parts (1) and (2) of Theorem 13.21, free of
`θ`). -/
def HoweDualityUnitarySplitStatement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Invertible (2 : F)] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuadraticInvolution c δ) (α ν : Type) [Fintype α]
    [DecidableEq α] [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (χ : Eˣ →* Circle) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    (ψ : UnitaryAdditiveCharacter F),
    HoweDuality (pairWeil c ν ψ χ Q hE hQ hQu hχ hres)

/-- The Weil representation in the statement is that of the splitting `pairSplitting` of the
dual pair (GKT Definition 13.15). -/
theorem howeDualityUnitarySplit_weil_pairSplitting {F : Type} [Field F] [CharZero F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
    {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    [Algebra.IsQuadraticExtension F E] {c : E →ₐ[F] E} {δ : E} (hE : IsQuadraticInvolution c δ)
    {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] {Q : Matrix α α E}
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) {χ : Eˣ →* Circle} (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {ψ : UnitaryAdditiveCharacter F} :
    HoweDuality (pairWeil c ν ψ χ Q hE hQ hQu hχ hres) ↔
      HoweDuality (pairSplitting (ν := ν) (ψ := ψ) hE hQ hQu hχ hres).weil := by
  rw [weil_pairSplitting]

end Langlands.Theta
