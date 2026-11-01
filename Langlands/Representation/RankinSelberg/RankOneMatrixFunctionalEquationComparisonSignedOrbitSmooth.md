# Smoothness of the actual signed matrix orbit

This internal derived module packages a determinant-weighted signed
inverse-transpose unipotent orbit of a matrix Schwartz–Bruhat test as an
actual smooth induced function with the same standard character. It makes
no gamma functional equation or compact extraction assertion.

The field is every canonical `F : PadicField.{uF} p`, with `p` prime. Its
canonical topology, valuation, local-field, Hausdorff, countability and Borel
structures are installed. The size is `n + 1` for every natural `n`,
including zero. Write `W = rankOneSignedWeyl n`, `iota` for inverse
transpose, `χ = standardCharacter ψ n`, and `abv` for the canonical
normalized absolute value. The character `ψ` is arbitrary.

For an ambient matrix Schwartz–Bruhat test `Θ`,
`signedMatrixOrbit F ψ n Θ g` is the actual totalized Bochner integral

```text
∫ u ∈ N, χ(u)⁻¹ Θ((iota(u) W⁻¹ g).val) du.
```

The measure is the existing `unipotentHaar F.Carrier n`.
`signedMatrixOrbit_left` proves covariance under `g ↦ u g` with multiplier
`χ(u)`. It uses the exact signed reflection and right Haar substitution of
SignedReflection. Thus its character is the same standard character.

`exists_signedMatrixOrbit_congruence` proves one principal congruence level
fixes this entire function under right translation, as do all deeper levels.
The published `RankOneIwasawa.exists_schwartz_congruence` gives the same
uniform right invariance of the ambient test at every matrix. Matrix
associativity moves right multiplication inside the orbit integrand, so
pointwise equality of integrands proves equality of total integrals.
This argument does not differentiate under the integral or assume parameter
continuity of an integral.

`weightedSignedMatrixOrbit F ψ n s Θ g` multiplies this orbit by
`determinantWeight abv g s`, for any complex exponent `s`.
`weightedSignedMatrixOrbit_left` retains standard-character covariance:
the determinant character is trivial on the actual upper unipotent group.
`exists_weightedSignedMatrixOrbit_stabilizer` intersects the principal
congruence subgroup just obtained with the kernel of the determinant-power
character. Both subgroups are open. Openness of the latter uses the
canonical absolute value's open norm-one group and the published
`Shahidi.isOpen_ker_determinantPower`. This supplies one open subgroup
fixing the whole weighted function.

`weightedSignedMatrixOrbitSmooth` uses `Induction.smoothFunctionOf` with
these exact covariance and open stabilizer proofs. Its evaluation is
definitionally `weightedSignedMatrixOrbit`, as stated by
`weightedSignedMatrixOrbitSmooth_eval`.
`weightedSignedMatrixOrbit_locallyConstant` and
`continuous_weightedSignedMatrixOrbit` follow from the published evaluation
theorem for smooth induction and local constancy implying continuity.

All integral identities use Lean's totalized Bochner integrals. This module
does not assert their absolute convergence; product convergence in the
Fourier comparison is supplied separately by SignedOrbitFourier and
SignedGLFourier. In particular, no invertible-support premise on `Θ` is
needed here. One may apply this construction to the actual rectangular
Fourier transform, bundled as a Schwartz–Bruhat function by the existing
self-dual Fourier equivalence for a supplied measure. The module itself
needs no additive Haar measure or self-duality premise.

The provenance is source-free derived content. SignedReflection supplies
the exact signed orbit covariance, RankOneMatrixUnipotentIntegral supplies
uniform congruence invariance of an arbitrary matrix test, WeightedSynthesis
supplies the determinant character's triviality on unipotents, and the
published smooth induction constructor packages the result.
