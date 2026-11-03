# Archimedean Iwasawa existence adapted to an actual Levi subgroup

Author: Worker 112.

`Langlands.Global.InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement`
is an unproved proposition definition. Fix a number field `F : Type u`,
an actual connected reductive group scheme `G/F`, an actual parabolic
inclusion `p : P → G`, a specified rational Levi inclusion `l : M → P`,
and an infinite place `v`. The proposition asks for a subgroup `K` of the
existing group `InfinitePlaceGroupPoints F G v` such that:

1. `K` is compact and maximal among compact subgroups of `G(F_v)`.
2. The literal ordered product `image(P(F_v)) K` is all of `G(F_v)`.
3. `image(P(F_v)) ∩ K = image(M(F_v)) ∩ K`, using `l ≫ p` for the
   second image.
4. The inverse image of `K` under `M(F_v) → G(F_v)` is compact and
   maximal among compact subgroups of the actual group `M(F_v)`.

`IsMaximalCompactSubgroup` expresses compactness and maximality in a
completion-point group. `IsLeviCompatibleIwasawaCompact` packages these
four properties for supplied data. The statement universally quantifies
over the field, connected reductive group, parabolic, specified Levi
and place, then existentially quantifies `K`. It supplies no compact
subgroup, Iwasawa coverage or point-topology comparison as an assumption.

The Levi premise is the existing `IsRationalLeviSubgroup l`. It means
that `M` is a connected reductive closed subgroup and that multiplication
with a represented geometric unipotent radical gives an isomorphism of
schemes over `F`. The parabolic premise is the existing
`IsParabolicSubgroup p`. No splitness or isotropy premise is added.
Improper parabolics and anisotropic groups remain in scope.

## Actual points, topology and intersection

The carrier is unchanged from
[`InfiniteAdelicGroupProduct`](InfiniteAdelicGroupProduct.md):
`G.affinePoints (CommAlgCat.of F v.Completion)`, the actual scheme points
over the number-field completion. Its group law is the group-object
law. Its topology is the existing topology induced by evaluating all
global regular functions in `v.Completion`. The same convention is used
for `M`; compactness in clause 4 is measured in that topology.

The maps in the products, intersections and inverse image are the
existing `affinePointsTarget` homomorphisms. They are induced by the
actual scheme maps `p` and `l ≫ p`, with no substitute point groups.
Clause 3 is equality of subsets of `G(F_v)`. Clause 4 uses the subgroup
`K.comap` in `M(F_v)`, so it states maximal compactness on the Levi
carrier without presupposing a topological identification with its
image in `G(F_v)`.

The proved helper `IsLeviCompatibleIwasawaCompact.mem_levi` rewrites
clause 3: any point in both the parabolic image and `K` lies in the
Levi image. This is a direct set-theoretic consequence of supplied
compatible compact data; it is not an existence proof.

## Source and specialization

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Appendix B, Theorem B.4.1 and its proof, printed p.547 (one-based PDF
p.552), gives a stronger simultaneous assertion. Fix a minimal
parabolic and its Levi over an archimedean local field. One maximal
compact works for every standard parabolic pair, with Iwasawa coverage,
maximal compact Levi intersection, and equality of the parabolic and
Levi intersections. Registered source:
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The original page was read as text and image. The complete registered
October 2026 author errata was read in the preceding work on this
block and has no Appendix B correction:
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The present target specializes the source to a single supplied pair
and number-field completions. To apply the source, base change `(P,M)`
to `F_v` and choose a minimal local parabolic inside that parabolic
whose minimal Levi lies in the supplied Levi. The resulting pair is
standard for that local choice. Applying B.4.1 gives clauses 1–3.
The closed Levi inclusion identifies its local points homeomorphically
with the image, transferring the source's maximal compact intersection
to the inverse-image formulation in clause 4. These base-change,
local minimal-pair and point-topology facts are required parts of a
proof, not hypotheses added to the Lean proposition. A parabolic
minimal over `F` need not remain minimal over `F_v`; the specialization
does not assume otherwise.

The source proof uses Lie-theoretic Iwasawa decomposition, maximal
compact conjugacy and component results, and Harish-Chandra's
compatible Levi choice. Its citations to Knapp Proposition 7.31 and
Harish-Chandra Lemma 8 are external proof inputs, not existing Lean
proofs. Any formal proof must supply the needed results or verified
current reuse bridges and preserve the existing evaluation topology.

## Consumer boundary

This target adds the Levi-intersection conclusions missing from
[`InfinitePlaceIwasawaStatement`](InfinitePlaceIwasawaStatement.md).
The existing `ParabolicIwasawaStatement` remains unchanged. Here `K`
may depend on the specified pair and place; no simultaneous choice
across different parabolics is asserted. The proposition also does not
assert existence of rational Levis for all parabolics.

For the canonical minimal parabolic and Levi in an actual Siegel setup,
clause 3 is the needed archimedean good-position input. Combining it
with centrality of the split torus in that Levi and the support
properties of positive adelic torus points is a further consumer
argument. Nonarchimedean compact choices, almost-everywhere integral
compatibility, adelic assembly, compatible Siegel reduction and finite
volume remain separate obligations. None is proved by this module.
