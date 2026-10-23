# Naturality of the Harris complex group splitting

This module proves that the actual Harris matrix and group splittings
in `ComplexGroupSplitting` commute with change of complex coefficient
algebra. It also constructs the target group-valued functor. All results
are internal consequences of the imported explicit algebra equivalences,
tensor maps and group projections.

## Target functor

For a commutative ring homomorphism `f : S →+* T`,
`ComplexMatrix.splitGroupMap n I f` sends a family of invertible square
matrices and an invertible scalar to

\[
 ((a_\tau)_\tau,c)\longmapsto((f(a_\tau))_\tau,f(c)).
\]

Here the matrix map applies `f` to every entry and the maps on units are
induced by the actual matrix and scalar ring homomorphisms. Thus their
inverses are carried along as part of their unit data. Preservation of
one and multiplication follows componentwise from those unit
homomorphisms. `splitGroupMap_id` and `splitGroupMap_comp` prove the
identity and composition laws by equality of unit values.

`splitGroupFunctor n I` packages these maps into a functor on all
commutative complex algebras with value

```
(I → (Matrix (Fin n) (Fin n) S)ˣ) × Sˣ.
```

The functor needs no finiteness or decidable equality on `I`. Its
identity and composition fields are proved by the preceding laws.

## Matrix and group naturality

Retain the actual number fields, algebra, involution, signature charts
`C`, and finite basis `b` required by `HarrisSignatureCharts`. Let `S,T`
be commutative complex algebras in the same universe, each supplied with
a real algebra structure compatible with `ℝ → ℂ`, and let
`f : S →ₐ[ℂ] T` be any complex algebra homomorphism.

`iteratedScalarMatrixEquiv_natural` proves that changing coefficients
in `S ⊗[ℝ] (ℝ ⊗[ℚ] A)` and then taking the actual Harris matrix
coordinates is the same as applying `f` entrywise to both ordered
matrix coordinates. The proof uses tensor induction. On pure tensors,
the existing matrix formula and compatibility of `f` with the complex
scalar maps give entrywise equality. Additivity proves the sum case.

`iteratedScalarGroupSplitting_natural` proves the same compatibility
for the actual iterated scalar-extension similitude group and
`splitGroupMap`. Equality of the first matrix units follows by projecting
the matrix naturality theorem and applying extensionality of units; the
multiplier equality is equality of the explicitly mapped scalar units.
This theorem uses the existing `baseChangeMap` on actual similitudes.

Assume additionally that `S,T` have rational algebra structures
compatible with `ℚ → ℝ`. `scalarMatrixEquiv_natural` proves the same
ordered matrix formula for the direct scalar extension `S ⊗[ℚ] A`.
It combines the established naturality of the actual tensor-tower
comparison with the iterated matrix formula.

Finally `scalarGroupSplitting_natural` proves that the directly extended
Harris group splitting commutes with the actual rational
`baseChangeMap` induced by `f`. The proof again compares matrix-unit
values and the scalar multiplier. The coefficient map for rational
scalar extension is the restriction of `f` first to `ℝ` and then to `ℚ`,
so the stated compatible scalar structures are respected explicitly.

## Scope and provenance

No naturality comparison is assumed as input. The module proves it
from tensor formulas, actual coefficient-change maps and the explicit
splitting. The coefficient rings can have nilpotents and need not be
fields. The same-universe restriction on `S,T` matches the category of
commutative coefficient algebras and the imported `baseChangeMap`.

The target functor is constructed, and naturality is proved for both
actual group splittings. This module does not yet package them as a
natural isomorphism with a chosen complex-base-change source functor,
or construct the resulting isomorphism of group schemes. Smoothness,
reductivity and the PEL scheme levels remain subsequent obligations.
