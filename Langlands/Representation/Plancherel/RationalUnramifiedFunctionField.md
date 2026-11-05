# Scalar ring and fraction field of actual unramified families

Author: Worker 1615.

This is a derived algebraic construction from the published
`rationalUnramifiedLaurentAlgebraEquiv` and Mathlib's finite-generation,
Noetherian-ring, monoid-algebra and localization results. It supplies scalar-ring
properties and a fraction field for the actual algebra used in the existing
unramified operator-family predicates. It does not prove rationality of a
standard intertwiner.

## Actual scalar algebra and hypotheses

The field `F : Type u` has instances `Field F`, `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F`. The group scheme is
`G : GroupScheme (Spec (CommRingCat.of F))`. Its rational-point group has a
supplied topology. The two displayed hypotheses are

```text
hp : Continuous (rationalValuationImageProjection G)
hG : GroupScheme.IsConnectedReductive G.
```

Write `B` for the existing algebra

```text
unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul).
```

Thus the parameter family contains all rational norm characters of the actual
group, and `B` is the existing evaluation-generated subalgebra of functions on
its actual continuous unramified characters. No assertion is made here for an
arbitrary norm family. There is no restriction on the characteristic, splitness
or quasisplitness of `G`, and the case `rationalImageRank G = 0` is included.

## Finite generation, Noetherianity and the domain property

The imported `rationalUnramifiedLaurentAlgebraEquiv G hp hG` identifies
`AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ)` with `B` as complex
algebras. The additive group of integer vectors with this finite index set is
finitely generated. Mathlib's finite-type instance for the additive monoid
algebra and transport along that equivalence prove
`rationalUnramifiedRegularFunctions_finiteType : Algebra.FiniteType ℂ B`.
Since the complex field is Noetherian, the finite-type algebra theorem gives
`rationalUnramifiedRegularFunctions_isNoetherianRing : IsNoetherianRing B`.

The integer-vector group has the unique-sums property, so its additive monoid
algebra over the complex field is a domain by Mathlib's monoid-algebra
instances. Transport through the inverse Laurent equivalence proves
`rationalUnramifiedRegularFunctions_isDomain : IsDomain B`. This uses the
finite Laurent description; merely viewing `B` inside a ring of all functions
would not justify the domain property.

## Fraction field and faithful inclusion

`rationalUnramifiedFunctionField G hp hG` is `FractionRing B`, retaining the
displayed hypotheses as explicit parameters. Its field instance is the
fraction-ring field instance after supplying the proved domain property.
The module also supplies the usual `B`-algebra and `IsFractionRing B` instances.

`rationalUnramifiedFunctionField_algebraMap_injective` states that
`algebraMap B (rationalUnramifiedFunctionField G hp hG)` is injective. The proof
uses Mathlib's injectivity theorem for the scalar map into a fraction ring.
Fractions are algebraic localization elements: this construction does not
extend evaluation of every fraction to every actual character, nor does it
assert that a nonzero regular function is everywhere nonzero.

## Application boundary

These are internal consequences of the already published coordinate-algebra
comparison. They supply neither actual induced or Jacquet families, their
filtrations and specialization comparisons, exponent separation, a denominator
nonvanishing on the whole required region, convergence nor the conditional
parabolic intertwining theorem. Those remain separate proof obligations.
