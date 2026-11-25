# Restriction and requotienting of faithful field-point tests

This internal module works over a complete ultrametric normed field `K`
and a normed extension field `L`, with independent algebra, small
space and extension-field universes.

For any bounded algebra map between presented affinoid algebras with
spectra small in universe `v`, the induced map on their small
saturated spectra retains exactly that bounded map on their global
charts, after the recorded equalities between global chart algebras
and original algebras. The proof uses the actual saturation-extension
formula on original charts. Under completeness of `L` and
`DomainCompletedResidueSurjectivityStatement`, this proves naturality
of the full field point constructed from any bounded character.
Mapping the character's full field point gives the full field point
of the composite character. Equality includes every evaluation,
using injectivity of global-chart evaluation.

Suppose bounded characters `χ : R → L` and `ψ : S → L` are related
by a bounded map `φ : S → R` with `χ ∘ φ = ψ`. The construction
`FaithfulCharacterQuotient.descend` sends `S / ker ψ` to
`R / ker χ`, using the actual presented closed quotients. It
commutes with the two quotient maps and with the descended faithful
characters. The induced map is injective: compose equality of its
values with the target's faithful character and use faithfulness
of the source quotient's character.

This construction applies when `R` is a local chart algebra and
`φ` is restriction from a larger chart. The local evaluation is
quotiented by its own kernel, which may differ from the kernel on
the larger chart. No local faithfulness premise is assumed.

When both original spectra are small in `v`, their quotient spectra
remain small in `v`. The induced algebra map therefore gives the
actual contravariant `testMap` between their small saturated test
sources. The full quotient test points are natural under this map,
under the same explicit completed-residue comparison and coefficient
completeness premises. This statement concerns complete full field
points, not only the points of the underlying topological spaces.

The provenance is internal: bounded closed-quotient descent,
faithful-character factorization, actual small-spectrum maps and
the global-chart full-field-point equivalence. No preservation of
arbitrary localized analytic pullbacks is asserted.
