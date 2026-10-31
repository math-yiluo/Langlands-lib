# Actual determinant images of finite and local automorphic realizations

This internal construction uses actual subspaces of the published automorphic
form space. The number field `F : Type u` has arbitrary universe, the natural
rank `n` includes zero, and coefficients are complex. All spaces inherit their
existing submodule topology. A finite-order continuous Hecke character `χ`
acts by the published multiplier

```text
Mχ f(a) = χ(det a) f(a).
```

`HeckeCharacter.finiteLocalDeterminant` is the continuous character obtained by
composing the actual adelic determinant character with `AdelicGL.ofFinite`
and the identity-supported `FiniteAdelicGL.localInclusion` at the specified
finite place. Its definition and application formula do not require finite
order. The finite-order hypothesis is required when restricting multiplication
to the actual automorphic form space.

For both `FiniteRealization` and `LocalRealization`, `determinantTwist`
constructs the image of the original form submodule under `Mχ`. Stability
follows from the published positive-right-translation covariance

```text
R(g)(Mχ f) = χ(det g) Mχ(R(g)f).
```

The finite case uses the actual finite adelic inclusion; the local case uses
the specified identity-supported local inclusion. Closure of a submodule
under complex scalar multiplication proves stability. The local covariance
on all forms is also exposed as
`AutomorphicForms.localRightAction_determinantMultiplier`.

In each namespace, `determinantTwistEquiv` is the restriction of the published
continuous complex-linear automorphism to its actual image, using
`ContinuousLinearEquiv.ofSubmodules`. Its value formula identifies the
underlying form with `Mχ f`. The representation covariance is proved by
subtype inclusion. `determinantTwistRepresentationEquiv` bundles the same
linear map as a genuine representation equivalence from the existing
`Langlands.twist` of the source action to the action on the constructed
image. Its application formula is definitional. The scalar is positive
`χ(det g)`, in agreement with the published convention
`R(g)f(a) = f(a g)`.

The continuous-function and evaluation formulas identify the forward map
with `Mχ` and the inverse map with multiplication by `χ(det a)⁻¹`.
`determinantTwist_eq_bot_iff` proves that the image is zero exactly when the
original subspace is zero: injectivity of the multiplier proves reflection,
and a linear map sends the zero submodule to zero. Its negation gives
`determinantTwist_ne_bot_iff`. `determinantTwist_mono` follows from
monotonicity of submodule image.

`FiniteRealization.toLocal_determinantTwist` proves equality of the actual
embedded local subspaces obtained by the two orders of construction.
Both underlying submodules are the same image under the same multiplier;
subrepresentation extensionality supplies the equality. Local restriction
retains the whole finite carrier, as in the published `toLocal`.
The constructed spaces retain smoothness by the existing
`FiniteRealization.isSmooth` and `LocalRealization.isSmooth` theorems.

The provenance is internal: this is submodule image and continuous
restriction applied to the published actual multiplier, actual finite/local
actions and existing scalar twist. No new external-source identification is
claimed. The generic private helpers prove image stability, zero reflection
and scalar-twisted equivariance; the public constructors use only the actual
form space.

These constructors require a supplied actual finite or local invariant
subspace. They assert no nonzero occurrence, tensor factorization,
identification of a factor with the whole local restriction, admissibility,
irreducibility, central-character or cuspidal transport, Satake comparison,
or weak-association compatibility.
