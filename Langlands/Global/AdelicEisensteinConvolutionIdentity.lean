import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicInducedRightTranslate
import Langlands.Global.AdelicEisensteinHarishChandraEquations

/-! # Right convolution of Eisenstein series where the series converges

For a continuous compactly supported `φ` on `G(𝔸)` and a parameter `λ` at which the terms of the
Eisenstein series of `v` are dominated by a summable sequence uniformly on `x · supp φ`,
`R(φ) E(v, λ)(x) = E(I(λ, φ) v, λ)(x)` with the integrated normalized action
`I(λ, φ) v (y) = ∫ φ(h) e^{-⟨λ, H_P(y)⟩} (v e^{⟨λ, H_P⟩})(y h) dh`
(`IsIwasawaCompact.rightConvolution_eisensteinSeries_eq_inducedConvolution`, from the termwise
identity `IsIwasawaCompact.rightConvolution_eisensteinSeries`). The Eisenstein series is linear
in the inducing function where the terms are summable
(`IsIwasawaCompact.eisensteinSeries_sum_mul`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The integrated normalized action `I(λ, φ) v (y) = ∫ φ(h) T_{λ,h} v (y) dh`, for the
twisted right translates `T_{λ,h} = hK.inducedRightTranslate λ h` and the Haar measure of
`G(𝔸)`. -/
def IsIwasawaCompact.inducedConvolution (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (φ v : AdelicGroupPoints F G → ℂ)
    (y : AdelicGroupPoints F G) : ℂ :=
  ∫ h, φ h * hK.inducedRightTranslate lam h v y ∂(Measure.haar : Measure (AdelicGroupPoints F G))

omit [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- Twisting `I(λ, φ) v` gives the right convolution of the twisted function. -/
theorem IsIwasawaCompact.parameterTwist_inducedConvolution (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (φ v : AdelicGroupPoints F G → ℂ)
    (y : AdelicGroupPoints F G) :
    hK.parameterTwist (hK.inducedConvolution lam φ v) lam y =
      ∫ h, φ h * hK.parameterTwist v lam (y * h)
        ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
  rw [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.inducedConvolution, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  change φ h * hK.inducedRightTranslate lam h v y * hK.heightPower lam y = _
  rw [mul_assoc, ← IsIwasawaCompact.parameterTwist, hK.parameterTwist_inducedRightTranslate]

/-- **Right convolution of a convergent Eisenstein series.** If the terms of the Eisenstein
series of a continuous `v` at `λ` are bounded on `x · tsupport φ` by a summable sequence, then
`R(φ) E(v, λ)(x) = E(I(λ, φ) v, λ)(x)`. -/
theorem IsIwasawaCompact.rightConvolution_eisensteinSeries_eq_inducedConvolution
    (hK : IsIwasawaCompact p K)
    {φ : AdelicGroupPoints F G → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {v : AdelicGroupPoints F G → ℂ} (hv : Continuous v) (lam : ComplexCharacterParameter F P)
    (x : AdelicGroupPoints F G) {b : ParabolicRationalCosets F p → ℝ} (hb : Summable b)
    (hbound : ∀ c, ∀ h ∈ tsupport φ, ‖hK.eisensteinTerm v lam (x * h) c‖ ≤ b c) :
    rightConvolution F G φ (hK.eisensteinSeries v lam) x =
      hK.eisensteinSeries (hK.inducedConvolution lam φ v) lam x := by
  rw [(hK.rightConvolution_eisensteinSeries hv lam hφc hφs x hb hbound).2]
  unfold IsIwasawaCompact.eisensteinSeries
  refine tsum_congr fun c => ?_
  rw [IsIwasawaCompact.eisensteinTerm, hK.parameterTwist_inducedConvolution]
  rfl

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
/-- The Eisenstein series is linear in the inducing function at points where the terms of each
summand are summable. -/
theorem IsIwasawaCompact.eisensteinSeries_sum_mul (hK : IsIwasawaCompact p K) {m : ℕ}
    (w : Fin m → AdelicGroupPoints F G → ℂ) (b : Fin m → ℂ)
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F G)
    (hsum : ∀ i, Summable (hK.eisensteinTerm (w i) lam x)) :
    hK.eisensteinSeries (fun y => ∑ i, b i * w i y) lam x =
      ∑ i, b i * hK.eisensteinSeries (w i) lam x := by
  unfold IsIwasawaCompact.eisensteinSeries
  calc
    _ = ∑' c, ∑ i, b i * hK.eisensteinTerm (w i) lam x c := by
      refine tsum_congr fun c => ?_
      simp only [IsIwasawaCompact.eisensteinTerm, IsIwasawaCompact.parameterTwist,
        Finset.sum_mul, mul_assoc]
    _ = ∑ i, ∑' c, b i * hK.eisensteinTerm (w i) lam x c :=
      Summable.tsum_finsetSum fun i _ => (hsum i).mul_left (b i)
    _ = _ := Finset.sum_congr rfl fun i _ => tsum_mul_left

end Langlands.Global.AdelicGroupPoints
