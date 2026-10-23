# The Hodge function and reflex field of the constructed real Harris homomorphism

Author: Worker 57.

This module computes the Hodge function of the positive complex homomorphism
constructed on the actual algebra `ℝ ⊗[ℚ] A` in
[RealPositivity](RealPositivity.md), using its assembled matrix coordinates.
It identifies this function with the previously computed standard function,
then computes its fixed-field reflex field. In the Harris CM type the field is
the distinguished image of the CM center in the nonexceptional case. In rank
two with one real place it is the rational subfield of `ℂ`.

## Inputs and conventions

The chart-level declarations use number fields `E` and `K`, with `E` totally
real, `K` totally complex, and a quadratic `E`-algebra structure on `K`.
The ring `A` has compatible `ℚ`, `E`, and `K` algebra structures as stated in
the Lean declarations, a second-kind involution `σ`, and Harris signature
charts `C : HarrisSignatureCharts σ n Φ`. These charts retain `1 < n`, a
distinguished real embedding, involution-compatible matrix equivalences at
the real embeddings, and their prescribed action of the center through `Φ`.
A finite `E`-basis `b` of `A` is supplied at this level.

The central-simple specialization uses
`D : CentralSimpleUnitaryData E K A n`, including the `E/K/A` scalar tower,
and derives its finite basis as `D.totallyRealBasis`. Its final constructor
`D.realReflexFieldOfSignature` takes `HasHarrisSignature` and
`IsCMSection E K Φ` proofs and constructs the charts from them. Neither a
positive homomorphism, a basis, nor a reflex field is an extra argument of
this final constructor.

The homomorphism used here is the underlying value of
`C.realPositiveKottwitzHom b`. Thus it is the complex conjugate of the
corrected Harris real algebra homomorphism. This is the `h₀` convention of
[Reflex](Reflex.md); passage from `h₀` to the associated Deligne group map
also involves inversion on complex units.

## Construction and calculation

Write `e = C.realMatrixEquiv b` for the constructed real algebra equivalence
from `ℝ ⊗[ℚ] A` to the product of complex matrix algebras, and write `h₀` for
the positive Kottwitz homomorphism. The theorem
`C.realPositiveKottwitzHom_matrix` proves

```text
e ∘ h₀ = (kottwitzHom n (E →+* ℝ) C.distinguished).hom.
```

The proof evaluates both homomorphisms at a complex number and then at
each real embedding. It applies `realComplexHom_matrix` to the conjugate
complex number. The equality therefore identifies the coordinates of the
constructed homomorphism itself.

`C.realHodgeFunction b` is `standardHodgeFunction Φ (e ∘ h₀)`.
The imported definition takes the complex dimension of the subspace on
which the selected matrix factor acts by multiplication by `z`; for the
conjugate embedding it uses entrywise conjugation of that factor. The theorem
`C.realHodgeFunction_eq` identifies this function with `C.hodgeFunction` by
the preceding homomorphism equality. Under `IsCMSection E K Φ`,
`C.realHodgeFunction_apply` gives its values, with `i₁ = Φ C.distinguished`:

| Embedding `i` | Value |
| --- | --- |
| `i₁` | `n - 1` |
| the conjugate of `i₁` | `1` |
| any other selected embedding `Φ τ` | `n` |
| any other conjugate embedding | `0` |

The definition `C.realReflexField b` is the fixed field in `ℂ/ℚ` of the
stabilizer of this actual coordinate Hodge function under `Aut(ℂ/ℚ)`.
`C.realReflexField_eq` identifies it with the standard `C.reflexField`.

## The two fixed-field calculations

For `n = 2` and `[Subsingleton (E →+* ℝ)]`, the imported
`C.hodgeStabilizer_eq_top` says that the standard Hodge function has the full
automorphism group as stabilizer. Applying the published theorem
`complexFixedField` to the bottom intermediate field proves
`C.realReflexField_eq_bot`. Here `⊥` is exactly the image of `ℚ` in `ℂ`.

For the Harris CM type, take an imaginary quadratic number field `F`, an
embedding `j : F →+* K`, and `τ₀ : F →+* ℂ`, and use
`Φ = harrisCMSection E j τ₀`. Under the explicit condition

```text
3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished,
```

`C.realReflexField_eq_distinguishedImage` proves that the reflex field
equals `C.distinguishedImage`, the image of `K` under the distinguished
complex embedding. It uses the standard stabilizer calculation from
`Reflex` and discharges that calculation's fixed-field hypothesis with
`complexFixedField`. There is no remaining `hgal` assumption.

The `CentralSimpleUnitaryData` namespace defines the corresponding Hodge
function and reflex field using the actual central-simple homomorphism
and its derived matrix equivalence. It proves the standard-function and
standard-field equalities and both field calculations by specializing
the chart-level results to `D.totallyRealBasis`.

## Provenance and scope

This is an internal derivation from the imported constructions in
`RealPositivity`, `Reflex`, and `ReflexGaloisProof`. The latter supplies
`complexFixedField` for every intermediate field of `ℂ/ℚ`. The original
source conventions of the standard Hodge function and its stabilizer
calculation are documented in [Reflex](Reflex.md); this module introduces
no additional external existence theorem.

The calculation now starts with the actual positive homomorphism on
`ℝ ⊗[ℚ] A` and its constructed real matrix equivalence. It uses the
coordinate definition of the Hodge function already in the Library. A
global complex tensor decomposition indexed by all embeddings of `K`,
independence under arbitrary changes of charts or conjugation of `h₀`,
and identification with a scheme-theoretic cocharacter conjugacy class
are not established here. Smoothness, reductivity, canonical models,
PEL representability, scheme level towers, and coefficient descent remain
separate obligations.
