# Renard A.IV.2: products and direct sums of abelian groups

Author: Worker 695.

This proof unit proves the four components of the unchanged published
`Langlands.Renard.AbelianGroupLimit.AbelianGroupLimitStatements`.
The index and group universes remain independent. The constructions use
the exact Cartesian-product and `DirectSum` vertices and the exact
lifted factors from the published statements.

The original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The example is at the end of A.IV.2, printed pages 257–258 / one-based
PDF pages 263–264, read in full for this proof. The original gives no
proof. The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19 were also read and contain no correction to this example.
The statement unit's uniform finite-support comparison and universe lifts
are internal packaging; the present proofs establish that exact packaging.

For a cone on the lifted factors, `cartesianProductStatement` takes each
leg, lowers its value by `AddEquiv.ulift`, and collects these homomorphisms
with `AddMonoidHom.pi`. Lifting a resulting coordinate recovers the
original leg. The leg equations force every coordinate of any competing
map to agree, establishing uniqueness.

For a cocone, `directSumCoproductStatement` raises an element of each
original factor and applies the corresponding cocone leg.
`DirectSum.toAddMonoid` extends that family to the direct sum. Its
single-generator evaluation formula establishes factorization;
`DirectSum.addHom_ext` establishes uniqueness.

`finiteSupportComparisonStatement` uses the faithful function coercion
for injectivity and `DFinsupp.finite_support` for one image inclusion.
For the reverse inclusion, a finite support set supplies a finset and
`DFinsupp.mk` constructs the corresponding finitely supported function.
Its coordinate formula proves equality with the original family.
`DFinsupp.single_eq_pi_single` identifies each direct-sum inclusion with
the full-product single-coordinate map.

For finite indices, `finiteProductCoproductStatement` obtains a `Fintype`
internally from the supplied `Finite` instance. It precomposes the same
direct-sum extension with the inverse of `DirectSum.addEquivProd`.
The equivalence sends single generators to the usual single-coordinate
families. The direct-sum extension theorem gives factorization, and
generator extensionality followed by surjectivity of the equivalence
gives uniqueness. No `Fintype` or decidable equality premise is added
to the theorem.

`abelianGroupLimitStatements` assembles these four proofs in the exact
order of the published conjunction. All four component theorems and the
aggregate are closed at arbitrary independent universes `uI` and `uG`;
classical index equality is internal. Empty indices are retained.

The proof reuses Mathlib's existing additive groups, homomorphisms,
dependent finitely supported functions and fan/cofan constructors at
commit `5ed2965256430c3649e86755f9576b54eca72435`.
It does not address the following filtered-colimit paragraph, any general
cone/cocone comparison, elementary or ordered shapes, subobject
intersections/unions, or original nonunital-module products. It does not
complete A.IV, Appendix A or the whole-book program.

Development verification used approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Check
`8b5574c2-24e2-4b07-808a-222d98e2b089` completed a Lake build with zero
errors or warnings. The aggregate inspection identifies a theorem with
level parameters `uI`, `uG` and only `propext`, `Classical.choice`, and
`Quot.sound`. This development check does not itself establish independent
acceptance or publication.
