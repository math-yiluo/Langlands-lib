# Positivity on the actual real Harris algebra

Author: Worker 57.

This internal construction transfers the positive twisted involution from the
standard matrix product to the actual real algebra `ℝ ⊗[ℚ] A`. It constructs
positive complex homomorphisms for both the corrected Harris convention and
the conjugated Kottwitz convention. The positivity certificates are proved
from the matrix splitting and regular trace; they are not inputs.

## Inputs and provenance

The general construction uses the same inputs as
`HarrisSignatureCharts.realComplexHom` in `RealSplitting`:

- a totally real number field `E`, a totally complex number field `K`, and
  a quadratic `E`-algebra structure on `K`;
- a ring `A` with `E`, `K` and rational algebra structures, with the
  rational-to-`E` scalar tower;
- a second-kind involution `σ`, Harris signature charts `C` for a family
  `Φ` of complex embeddings above the real embeddings, and a finite `E`-basis
  `b` of `A`.

The charts retain the rank and signature requirements from `HarrisLevels`.
Their real matrix equivalence is constructed in `RealSplitting`; no further
splitting or positivity hypothesis is imposed here.

For `CentralSimpleUnitaryData D`, the `E`-to-`K`-to-`A` scalar tower is also
retained. The basis comes from `D.totallyRealBasis`. The final constructor
`realPositiveKottwitzHomOfSignature` takes `HasHarrisSignature` and
`IsCMSection`, and obtains the charts from `HarrisSignatureCharts.ofSignature`.
It requires no separately supplied finite basis, chart family, positive
involution, or complex homomorphism.

The provenance is internal. `Positivity` already defines the regular-trace
positivity condition, the twist, conjugation, and the matrix positivity
certificate, with its original-source discussion of Kottwitz and Milne.
`RealSplitting` constructs the actual algebra equivalence and complex
homomorphism. This module combines those constructions using Mathlib's
`LinearMap.trace_conj'`. It asserts no new result from external literature.
The conjugation convention is inherited unchanged from those modules.

## Regular trace and transport

`trace_mulLeft_algEquiv` works over any commutative ring `R` and any
`R`-algebra equivalence `e : A ≃ₐ[R] B`. It proves

```text
Tr_R(L_(e x) : B → B) = Tr_R(L_x : A → A).
```

Conjugating left multiplication by the underlying linear equivalence gives
left multiplication by `e x`; Mathlib's trace-conjugacy theorem then applies.
No finite-dimensional hypothesis is needed for this equality: it uses
Mathlib's trace on arbitrary modules, which is zero when a finite free basis
does not exist.

`AlgebraInvolution.isPositive_iff_of_algEquiv` takes real involutions `σ`, `τ`
and an algebra equivalence intertwining them. Applying trace invariance to
`σ(x) x`, and using the equivalence to transport nonzero elements, proves
`σ.IsPositive ↔ τ.IsPositive`. The positivity predicate is exactly the
regular-trace predicate from `Positivity`.

`AlgebraInvolution.PositiveComplexHom σ` is the subtype of compatible complex
algebra homomorphisms whose twisted involution is positive. Its `conj`
operation precomposes with complex conjugation and proves the new certificate
using `ComplexHom.twist_conj`. The underlying homomorphism equality is
`PositiveComplexHom.conj_val`.

## The actual tensor algebra

For `e = C.realMatrixEquiv b` and `h = C.realComplexHom b`,
`realComplexHom_twist_matrix` proves

```text
e(h(-i) σ_R(x) h(i)) = (e x)*,
```

where `σ_R` is the rational involution extended to `ℝ`, and the right side is
conjugate transpose in every matrix factor. The implementation expands the
twist, applies the involution compatibility of `e` and the matrix formula for
`h`, then uses `correctedComplexHom_twist` at each real embedding.

The real embeddings form a finite type. Thus `piConjTranspose_isPositive`
and the transport equivalence prove `realComplexHom_twist_isPositive`.
`realPositiveComplexHom` packages this proved certificate with `h`.
`realPositiveKottwitzHom` conjugates that positive homomorphism. The two
`_val` identities show that their underlying homomorphisms are exactly the
previously constructed `h` and `h.conj`.

The central-simple namespace specializes each construction using the derived
basis. In particular `D.realPositiveKottwitzHom C` has underlying homomorphism
`(D.realComplexHom C).conj`, the same algebra homomorphism used before inversion
by `D.kottwitzDeligneMap` in `HarrisDeligneGroupScheme`. Positivity concerns its
twisted involution, rather than the inverse map on group points.

## Scope

This establishes regular-trace positivity on the original algebra's actual
real scalar extension. It supplies a constructed positive homomorphism with
explicit signature and CM-section hypotheses.

It does not assert positivity of the original untwisted involution, remove
the signature hypotheses, prove smoothness or reductivity of a group scheme,
or construct a PEL moduli scheme or its canonical model. Those geometric and
coefficient-system obligations remain separate.
