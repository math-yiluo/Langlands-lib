import Langlands.Global.RankinSelberg.SchwartzBruhatProof.PartA
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Fourier

/-! # Proof of the restricted-tensor description and Fourier inversion on `S(𝔸^n)`

Proof of `Langlands.Global.RankinSelbergGlobal.SchwartzBruhatStatement` (Getz–Hahn §C.3,
printed pp.553–554). The span equality is `schwartzBruhat_eq_restricted`
(`SchwartzBruhatProof.PartA`). Integrability of the Fourier integrand is
`EqualAnalytic.integrable_mul_pairing`, applied to the integrability of `Φ` from
`EqualAnalytic.schwartzBruhat_properties`. Fourier stability and inversion are
`fourierTransform_mem_and_inversion` (`SchwartzBruhatProof.Fourier`).
-/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof

open Langlands.Global.RankinSelbergGlobal.EqualAnalytic

/-- **Getz–Hahn §C.3, pp.553–554.** The two descriptions of `S(𝔸^n)` agree, and for a
standard additive character the Fourier transform is absolutely convergent on `S(𝔸^n)`,
preserves `S(𝔸^n)` and satisfies `Φ̂̂(x) = Φ(-x)`. -/
theorem schwartzBruhatStatement_proof : SchwartzBruhatStatement.{u} := by
  intro F _ _ _ n
  refine ⟨schwartzBruhat_eq_restricted n, fun ψ hψ Φ hΦ =>
    ⟨fun x => ?_, fourierTransform_mem_and_inversion n ψ hψ hΦ⟩⟩
  exact integrable_mul_pairing F n ψ hψ (schwartzBruhat_properties F n hΦ).2.1 x

end Langlands.Global.RankinSelbergGlobal.SchwartzBruhatProof
