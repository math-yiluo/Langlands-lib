# Dimension and compression bounds at a compact-open level

This internal supporting construction isolates two algebraic steps of Renard
VI.2.3–VI.2.4, French edition dated 9 July 2026, printed pp.140–142 /
PDF pp.146–148. Source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It applies to arbitrary topological groups, with independent group and
representation-carrier universes. It proves no actual reductive-group
uniform-support theorem.

`Langlands.Hecke.FixedLevelSandwich` records finite sandwich data inside the
actual compact-open corner `HeckeAlgebra.Corner μ K hK`. It consists of finitely
many edge elements, finitely many commuting middle elements, and the assertion
that their sandwich products span the corner. Its numerical `dimensionBound`
depends on these data alone, before choosing any representation.

The published `sandwichSimpleModuleDimensionBound` bounds a finite-dimensional
simple module by `size ^ (2 ^ generators)`. The implemented `finrank_le` applies
it to the actual fixed-vector module and its actual `cornerModule` action.
The required simplicity is
`CompactCoefficientClass.isSimpleModule_fixedVectors`; a zero fixed space is
handled separately. The import containing that simplicity lemma also contains
fixed-level finiteness results, but this argument uses none of those finiteness
conclusions. Compact smooth-dual coefficients supply finite-dimensionality
through `CompactCoefficientClass.finiteDimensional_fixedVectors`. For general
irreducible smooth representations finite-dimensionality remains an explicit
input.

The compression lemmas concern the published `Jacquet.compressedAction`:
act by a group element and average over the supplied compact open subgroup,
on its existing fixed-vector submodule. For an actual `IsIwahoriContraction`,
the published `powerKernelSup_eq_ker_of_iwahoriContraction` identifies the
union of the power kernels with the kernel of the actual Jacquet quotient
map. If the Jacquet relations fill the representation, this union is the
whole fixed space. Mathlib's stabilization of power kernels at the vector
space dimension therefore shows that any upper bound `d` on this dimension
annihilates compression to the power `d`. No positivity of `d` or nonzero
fixed-space assumption is required.

Multiplicativity of compression identifies this with compression by the
actual group power. For a left factor `a` that carries `K ∩ N` into `K` by
conjugation, the Iwahori lower and Levi conditions on the right factor
`g ^ d` give the same vanishing for `a * g ^ d`. Finally a linear map
invariant under `K` takes the same value before and after averaging. Thus
every such output vanishes on these translates of every `K`-fixed vector.
The exponent depends only on a bound on the fixed-space dimension and is
independent of the vector and output functional.

This proof uses vanishing Jacquet coinvariants in place of the source's
escape-of-powers and individual compact-coefficient argument. It leaves
construction of the sandwich data and a common fixed-space dimension bound
for the actual rational-point groups, the positive chamber decomposition,
and the common compact support comparison on the actual norm kernel as
separate obligations. No such structural conclusion is added as a premise
to the published uniform-support target.
