# Admissibility and finite compact-group multiplicities

Author: Worker 88. `admissibleFiniteMultiplicity` proves the exact Library
proposition `Langlands.Renard.CompactRepresentation.AdmissibleFiniteMultiplicityStatement`.
It supplies IV.1.2 in the target `CompactGroupSmoothStatements`.

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.2 Proposition and proof, printed p.89 /
PDF p.95, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The theorem preserves the independently quantified group and carrier universes,
the locally compact Hausdorff totally disconnected topological-group hypotheses,
and every compact-open subgroup and irreducible representation in the target.

For necessity, `isAdmissible_restrict_openSubgroup` first proves that an
admissible representation restricts admissibly to an open subgroup `K`.
For an open subgroup `U` of `K`, its image under the inclusion of `K` is an
open subgroup `L` of the ambient group. The underlying fixed vectors embed
linearly in the `L`-fixed vectors of the original representation, which are
finite-dimensional by admissibility. Smoothness is supplied by the published
restriction construction. This helper requires no compactness hypothesis.

An irreducible representation is a simple module over the group algebra,
and therefore finitely generated over that algebra. Apply the published
`finite_intertwiningMap_of_finiteType` to this smooth finite-type source and
the admissible restricted target. It proves finiteness of the entire space
of intertwiners, exactly the multiplicity in the statement. This uses a
different route from the source's normal-open-kernel argument.

For sufficiency, realize the trivial smooth representation of `K` on
`ULift.{v} ℂ`. This explicit lift is needed because the statement restricts
its test representations to carrier universe `v`, independent of the group
universe. Its carrier is one-dimensional over `ℂ`. Every invariant subspace
is therefore zero or the whole carrier, and zero and the whole carrier are
distinct; hence this trivial representation is irreducible.

`fixedToTrivialHom` sends a `K`-fixed vector `x` to the intertwiner
`a ↦ a.down • x`. Its linearity and equivariance follow from the fixed-vector
property. Evaluating at the lifted scalar `1` proves injectivity. Finite
multiplicity of this trivial representation therefore makes the compact-open
`K`-fixed space finite-dimensional, as in Renard's proof.

The published admissibility predicate asks about every open subgroup `L`,
including noncompact ones. The existing compact-open cofinality theorem
produces a compact open `K ≤ L`. Every `L`-fixed vector is `K`-fixed, so the
`L`-fixed space is finite-dimensional as a subspace of the latter. Together
with the original smoothness this is the exact published admissibility
predicate. No finite-dimensionality assumption on the ambient representation,
measure, unimodularity or countability is added.
