# Quadratic norm–trace expansion in supplied p-adic integer rings

Worker 84 specifies the internal derived proposition
`Langlands.LocalClassField.QuadraticNormTraceStatement.{u,v}`.
Worker 27 identified the pinned Mathlib determinant identity and its
localization route. This module defines the target and contains no proof.

For every prime `p`, the fields `F : PadicField.{u} p` and
`E : PadicField.{v} p` have independent arbitrary carrier universes.
The proposition uses their supplied `Algebra F.Carrier E.Carrier`,
compatible `IsScalarTower (Padic p) F.Carrier E.Carrier`, and finite
dimension. The integer rings are exactly `T.Integers` and `S.Integers`
of the arbitrary supplied topological data `T` and `S`.
For every `a` in the first integer ring and `y` in the second, it asks
for an actual `r : T.Integers` such that, in `F.Carrier`,

```text
N_E/F(1 + i(a)*y) = 1 + a*Tr_E/F(y) + a^2*r.
```

Here `i` is the supplied field algebra map; `Algebra.norm` and
`Algebra.trace` are the determinant and trace of multiplication on
that same extension. No alternative norm, ideal or trace is introduced.
The witness is integral in the actual base integer ring. There is no
Galois, unramified, prime-degree or nonvanishing condition, and the
quantifier includes `p = 2`, `a = 0`, `y = 0` and `1 + i(a)*y = 0`.

## Internal derivation and reuse

This is an internal consequence of the existing supplied-data
integer structures and pinned Mathlib, rather than a theorem attributed
to Henniart, Harris or Serre. At Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/RingTheory/NormTrace.lean`, `Algebra.norm_one_add_smul`,
states the corresponding identity for every finite free commutative
algebra, using a determinant expansion. The trace factor in Mathlib
is written on the left of `a`; commutativity gives the displayed order.

The current Library theorem
`Langlands.LocalClassField.NYLL.relativeIntegerStructure`, from
`Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof`,
gives relative finiteness and integral closure for these named integer
algebras. The named `relativeIntegerAlgebra`,
`relativeIntegerFieldAlgebra`, `relativeIntegerFieldTower` and
`relativeIntegerTower` in `Langlands.LocalField.RelativeIntegers`
retain the actual field map. Torsion-freeness and the base integer
ring's principal-ideal property give freeness. Integral closure supplies
the relative localization. Mathlib's `Algebra.norm_localization` and
`Algebra.trace_localization`, in
`Mathlib.RingTheory.Localization.NormTrace`, then identify the integer
identity with the displayed field identity. The private helper
`relativeNormData` in the public `UnitNormProof.lean` was inspected as
an implementation model; it is not an importable theorem or an extra
hypothesis. All named Library results retain their original authorship.

Taking `a = p^k` would put the error in `p^(2*k) O_F`. This explains
the intended first-order deep-unit consumer; the present statement
contains only the displayed equality with its integral witness.
It constructs no character, extension, finite image, ramification depth
or stabilizer, and does not assert logarithm or exponential identities.
