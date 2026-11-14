# Maximal tori exist étale-locally on an arbitrary base

Worker 584; source and proof correspondence contribution by Worker 632.

`Langlands.GroupScheme.etaleLocalMaximalTorusExistence.{u}` proves the unchanged
published `EtaleLocalMaximalTorusExistenceStatement.{u}`. For every scheme
`S : Scheme.{u}` and reductive group scheme over `S`, it constructs an étale
cover in universe `u` with a closed relative torus on each member that is
maximal on every residue-field fibre. There are no further hypotheses on
the base or group.

The source statement is Conrad, *Reductive group schemes* (2014),
Corollary 3.2.7, p.95.
The registered source is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
All cited page numbers are one-based PDF pages, equal to the printed pages.

The source deduces the corollary from the smooth surjective scheme of maximal
tori in Theorem 3.2.6, p.94. The implemented proof instead assembles the
published finite-Galois splitting, pointed split-torus lifting, and open
self-centralizing locus results directly. Its local geometric inputs
correspond to Proposition 3.1.6, pp.83–84, and Proposition 3.1.9(2), pp.85–86.
No theorem about the scheme of maximal tori is used.
The note after Proposition 3.1.9 on p.85 explicitly identifies field
maximal-torus existence as an input that permits this alternate route.

The internal transport lemmas are documented in
[`FibrewiseMaximalTransport`](FibrewiseMaximalTransport.md). The other helper
theorems in this module are derived constructions from the cited Library
results, rather than additional statements attributed verbatim to Conrad.

For `splitTorus.exists_affine_open_fibrewiseMaximal_of_fieldPoint`, the base
is affine and the input is a closed inclusion of a standard split torus that
is maximal at a supplied field point. The proof first reflects maximality
to the residue fibre at the image of that point. Published comparison
lemmas convert this to geometric maximality and hence membership in the
open geometric self-centralizing locus. An affine open neighbourhood
inside that locus is chosen. For each of its residue points, the proof
uses the geometric-locus characterization, reflection to the original
residue fibre, extension to the new residue field, and the base-change
composition comparison. The resulting actual inclusion is closed and
maximal on all residue fibres.

The variant
`splitTorus.exists_affine_open_fibrewiseMaximal_of_fieldPoint_overScheme`
handles an arbitrary base. A field spectrum has only one point, so the
supplied map factors through an affine chart containing its image. The
affine construction applies there, and the resulting inclusion is
transported through the ambient base-change composition isomorphism.

`exists_etale_affine_split_maximalTorus` applies the following construction
to each point `s` of the original base. First,
`exists_finiteGalois_hasSplitMaximalTorus`, supplied with the proved
`torusFiniteGaloisSplitting` and `maximalTorusBaseChange`, gives a split
maximal torus after a finite Galois extension of `κ(s)`.
This helper uses the published `maximalTorusExistence` over the original
residue field, then splits that torus and preserves maximality under the
field extension.
`etaleResidueExtension` realizes that extension as the residue field at
a point of an étale neighbourhood. The actual torus inclusion is
transported to this residue fibre by the recorded residue-field
isomorphism and base-change comparisons. Its published construction is
documented in
[`EtaleResidueExtensions`](../../AlgebraicGeometry/EtaleResidueExtensions.md)
and implements Stacks Tags 02LF and 00UD, with the exact original scalar
map retained; finite Galois extensions supply the required separability.

The proved `relativeSplitTorusLifting` lifts this closed split torus to
a further pointed étale neighbourhood. Its exact recovery equation,
through `isMaximalTorus_of_lifting_recovery`, ensures that the specified
lifted field fibre is still maximal. A split presentation converts the
lifted torus into a standard split torus. The preceding affine-open
construction then provides an affine open containing that field point
on which every residue fibre is maximal. Composition of the open immersion
and the two étale maps is étale. The point equations ensure that the image
contains `s`. The two successive ambient base-change comparisons identify
the final closed inclusion with one into the pullback of the original
group.

Finally, `etaleLocalMaximalTorusExistence` chooses one such affine étale
neighbourhood for every `s : S` and uses `Scheme.Cover.mkOfCovers`. The
index type is `S`, which lies in universe `u`, and all rings, finite torus
index types, and schemes constructed by the helper lie in that universe.
Each standard split torus is a relative torus by
`RelativeTorus.IsTorus.of_isSplitTorus`; closedness and fibrewise
maximality are supplied by the helper. This proves exactly the published
statement. The construction also provides affine cover members and split
tori, although the target requires neither refinement.
