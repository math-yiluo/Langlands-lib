import Langlands.BaseChange.LeviClassSystem
import Langlands.BaseChange.RelativeParabolicDiscriminant
import Langlands.BaseChange.TwistedCharacter.Saturation
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Group.GL.IntegralSubgroup
import Langlands.AllField.Group.GL.BlockModulus
import Langlands.LocalField.ResidueNormalization

/-! # Statement: local descent of the twisted constant term near a σ-regular point

This module states the local form of the passage from formula (2) to formula (3) in
Henniart–Lemaire (2011), II.4.5: near a σ-regular point `δ`, the twisted constant term of a
test function decomposes into pieces supported near the σ-conjugacy classes of the Levi
representatives `d j`, with integrals `|D_{G/M,σ}(d j)|_F^{-1/2} ∫ φ`. It supplies no proof.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis GeneralLinear JacquetLanglands

universe u v

/-- Local descent of the twisted constant term near a σ-regular point (the local form of
Henniart–Lemaire 2011, II.4.5, used to pass from (2) to (3)). Let `E` be a cyclic `F`-algebra
of group `⟨σ⟩` of order `l`, both nonarchimedean local fields, `δ ∈ GL_n(E)` norm associated
with a regular semisimple `γ ∈ GL_n(F)`, `m` a Levi class system for `γ` and `d j ∈ M(E)`
σ-conjugates of `δ` with blockwise cyclic norms the blocks of `m j`. Use the Haar measures of
`TwistedVanDijkStatement`. For every family of open windows `Ω j ∋ d j` in `M(E)` there is an
open neighbourhood `U₀` of `δ` such that for every test function `φ` supported in `U₀`, the
function `m ↦ δ_P(m)^{1/2} ∫_U ∫_K φ(k⁻¹ m u σ(k)) dk du` is a sum of test functions `ψ j`,
with `ψ j` supported in the union of the twisted conjugates `x Ω_j σ(x)⁻¹` (`x ∈ M(E)`) and
of integral `|D_{G/M,σ}(d j)|_F^{-1/2} ∫ φ`. -/
def TwistedLocalDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hE : IsCyclicAlgebra σ l), 0 < n → ∀ (B : BlockShape n)
    (δ : GeneralLinear n E) (γ : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
    ∀ (k : ℕ) (m : Fin k → B.Levi F), IsLeviClassSystem B γ m →
    ∀ (d : Fin k → B.Levi E),
      (∀ j, (∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = B.leviEmbedding E (d j)) ∧
        ∀ i, cyclicNorm σ l (d j i) = baseChange F E (B.size i) (m j i)) →
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    letI : MeasurableSpace (B.Levi E) := borel _
    haveI : BorelSpace (B.Levi E) := ⟨rfl⟩
    haveI : FiniteDimensional F E := hE.1
    ∀ (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
      (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
      (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
      (μK : Measure (GeneralLinearGroup.integralSubgroup (Fin n)
        (ValuativeRel.valuation E).integer)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK],
      μG (GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer) = 1 →
      μM {x | ∀ i, x i ∈ GeneralLinearGroup.integralSubgroup (Fin (B.size i))
        (ValuativeRel.valuation E).integer} = 1 →
      μU {y | (y : GeneralLinear n E) ∈
        GeneralLinearGroup.integralSubgroup (Fin n) (ValuativeRel.valuation E).integer} = 1 →
      ∀ (Ω : Fin k → Set (B.Levi E)), (∀ j, IsOpen (Ω j)) → (∀ j, d j ∈ Ω j) →
      ∃ U₀ : Set (GeneralLinear n E), IsOpen U₀ ∧ δ ∈ U₀ ∧
        ∀ φ : SchwartzBruhat (GeneralLinear n E), Function.support φ ⊆ U₀ →
          ∃ ψ : Fin k → SchwartzBruhat (B.Levi E),
            (∀ j, Function.support (ψ j) ⊆
              twistedConjugacySaturation (leviAut σ B).toMonoidHom (Ω j)) ∧
            (∀ j, ∫ x, ψ j x ∂μM =
              (((Real.sqrt (LocalField.residueNormalizedAbsoluteValue F
                (twistedRelativeParabolicDiscriminant B σ (d j))))⁻¹ : ℝ) : ℂ) *
                ∫ g, φ g ∂μG) ∧
            ∀ x : B.Levi E, ∑ j, ψ j x =
              ((LocalFieldData.ofInstances E).leviHalfModulus B x : ℂ) *
                ∫ y, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ * B.leviEmbedding E x *
                  (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ∂μU

end Langlands.BaseChange
