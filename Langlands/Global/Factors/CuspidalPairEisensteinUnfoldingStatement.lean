import Langlands.Global.Factors.CuspidalPairEisensteinOpenCell
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Unfolding the generic coefficient of a cuspidal-pair Eisenstein series

On a right half-plane, the generic Fourier coefficient of the Eisenstein series on
`GL_(r+t+2)` induced from an actual cuspidal pair is, up to a positive constant comparing Haar
measures, the integral over the open Bruhat cell of the Levi Whittaker coefficient of the
twisted section (Shahidi 1978, Lemma 2.1; Shahidi 1981, proof of Theorem 5.1). See the paired
Markdown. -/

set_option autoImplicit false

universe u

namespace Langlands.Global

open NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters and a standard
additive character `ψ`, there is a positive constant `κ` such that for every section `φ` of the
normalized induction from `π ⊗ π'^∨`, on some right half-plane the generic coefficient
`coeff ψ φ s` of the Eisenstein series equals `κ` times the open-cell integral
`∫_{U'(𝔸)} W_M(φ_s)(w u') conj(ψ_N(u')) du'` (`openCellIntegral`). -/
def CuspidalPairEisensteinUnfoldingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∃ κ : ℝ, 0 < κ ∧ ∀ φ, IsSection T T' φ →
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        coeff (r := r) (t := t) ψ φ s = (κ : ℂ) * openCellIntegral ψ φ s

end Langlands.Global
