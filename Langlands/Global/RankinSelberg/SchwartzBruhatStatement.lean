import Langlands.Global.RankinSelberg.SchwartzBruhat
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # The two descriptions of `S(𝔸^n)` and Fourier inversion

The span of the pure tensors `Φ_∞ ⊗ Φ_f` equals the span of the restricted pure tensors
`Φ_∞ ⊗ ⊗_(v ∈ S) Φ_v ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`; and for a nontrivial unitary character `ψ`
of `F \ 𝔸`, the Fourier transform for the covolume-one Haar measure is absolutely
convergent on `S(𝔸^n)`, maps `S(𝔸^n)` to itself and satisfies `Φ̂̂(x) = Φ(-x)`.
-/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- Getz–Hahn §C.3, printed pp.553–554: the restricted tensor product description of the
Schwartz–Bruhat space of `𝔸^n`, and Lemma C.3.1 with Fourier inversion (C.6) for the
self-dual (covolume-one) measure. -/
def SchwartzBruhatStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (n : ℕ),
    schwartzBruhat F n = restrictedSchwartzBruhat F n ∧
    ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      ∀ Φ ∈ schwartzBruhat F n,
        (∀ x : RowVector F n,
          Integrable (fun y : RowVector F n => Φ y * ψ (∑ j, y 0 j * x 0 j))
            (rectangleMeasure F 1 n)) ∧
        fourierTransform F n ψ Φ ∈ schwartzBruhat F n ∧
        ∀ x : RowVector F n,
          fourierTransform F n ψ (fourierTransform F n ψ Φ) x = Φ (-x)

end Langlands.Global.RankinSelbergGlobal
