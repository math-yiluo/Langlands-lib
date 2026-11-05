# Proof of the supplied-integer quadratic norm–trace expansion

Worker 84 implements `Langlands.LocalClassField.quadraticNormTrace.{u,v}`
with exact type `QuadraticNormTraceStatement.{u,v}`. Worker 27 supplied
the determinant-identity and localization route. Worker 1651 adopts their
unchanged Lean implementation and prepares this paired explanation for
independent review.

For every prime `p`, finite compatible extension of supplied p-adic fields
`E/F` in independent universes `u` and `v`, arbitrary supplied topological
data `T` and `S`, and actual integers `a : T.Integers` and
`y : S.Integers`, the theorem constructs `r : T.Integers` with

```text
N_E/F(1 + i(a)*y) = 1 + a*Tr_E/F(y) + a^2*r.
```

The norm and trace are the determinant norm and multiplication trace for
the supplied field algebra, and `i` is its algebra map.

The proof installs both supplied topologies, valuations and local-field
certificates, then the published named relative integer and field
algebras, their field tower and integer-inclusion tower.
`NYLL.relativeIntegerStructure` gives integral closure and relative
finiteness. Injectivity of the actual relative field map gives
torsion-freeness on integer rings, and the existing principal-ideal
structure gives module freeness. `IsIntegralClosure.isLocalization`
supplies the relative localization.

Mathlib's `Algebra.norm_one_add_smul a y` produces an integral witness
`r` in the base ring. The proof applies its inclusion into the base
field to that identity. `Algebra.norm_localization` identifies the
left side with the actual field norm, and
`Algebra.trace_localization` identifies the linear coefficient with
the actual field trace. Definitional equality of the named algebra
maps makes the image of `a • y` the stated product. Commutative ring
arithmetic puts the factors in the target's order.

This is an internal adaptation of pinned Mathlib and public Library
results listed in the target Markdown, using Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
The named integer structures and `NYLL.relativeIntegerStructure` are
imported from their public modules; the proof imports no private helper.
The argument retains every prime including two, arbitrary finite degree
and ramification, and zero or nonunit choices of `a` and `y`.
It uses no Galois or unramified assumption and no division by two.
It proves the exact field equality with an integral witness and no
character-theoretic conclusion.
