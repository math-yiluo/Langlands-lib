/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The coefficient setting for the Fourier--Deligne transform

Source: blueprint `sec-fourier-transform/def-fourier-set/def-fourier-set.md`
(blueprint: def-fourier-set).

The fixed finite-field datum and the finite coefficient extension used for the
Fourier--Deligne transform are bundled.  The six operations, compact supports,
cohomology, and Tate twists are the published six-functor constructions; this
structure records the coefficient hypotheses under which they are used.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace WeilConjectures

/-- The coefficient setting for the Fourier--Deligne transform.

The fields `field` and `coefficients` fix a prime `p`, a power `q = p ^ a`,
`k₀ = 𝔽_q`, its algebraic closure `k`, a prime `ℓ ≠ p`, and a fixed algebraic
closure `Qbar` of `ℚ_ℓ`.  The intermediate field `extension` is the finite
extension `E / ℚ_ℓ`; `rootsOfUnity_mem` is the standing assumption
`μ_p ⊆ E`, so additive characters with values in `μ_p` are `E`-valued.
The bounded constructible adic category and its six operations are the
published constructions on separated finite-type schemes over `k₀`.

Source: blueprint `sec-fourier-transform/def-fourier-set/def-fourier-set.md`
(blueprint: def-fourier-set). -/
structure FourierSetting where
  field : FiniteFieldDatum.{u}
  coefficients : field.CoefficientDatum
  extension : IntermediateField (Padic coefficients.l) coefficients.Qbar
  [finiteExtension : FiniteDimensional (Padic coefficients.l) extension]
  rootsOfUnity_mem :
    ∀ ζ : rootsOfUnity field.p coefficients.Qbar,
      ((ζ : coefficients.Qbarˣ) : coefficients.Qbar) ∈ extension

attribute [instance] FourierSetting.finiteExtension

end WeilConjectures
