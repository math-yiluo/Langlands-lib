# Point topology and compact-open cofinality for actual dynamic centralizers

`Langlands.Aubert.General.dynamicCentralizerPointHomeomorph` constructs a
multiplicative homeomorphism from the identity-test rational points of the
actual `Dynamic.Affine.centralizerScheme χ` to the subgroup given by
`Dynamic.centralizer χ` in the ambient rational points. This construction
works for every commutative ring `R : Type u` with a topology, every affine
group scheme `G` over `Spec R`, and every cocharacter `χ`. The source and
ambient topologies are their pinned `rationalPointTopology`; the target has
the subgroup subspace topology. Closedness of the published inclusion supplies
affineness of its source, so no separate affineness premise for the centralizer
is required.

The construction is the published `PointTopology.rationalPointSubgroupHomeomorph`
applied to the actual affine centralizer representative and its published
all-test representability and closedness proofs. The companion application
lemma states that its underlying ambient point is precisely postcomposition
with `Dynamic.Affine.centralizerHom χ`. It requires no Hausdorff, local-field,
finite-type or topological-group premise.

`Langlands.Aubert.General.dynamicCentralizer_compactOpenCofinal` holds for
every nonarchimedean local field `F : Type u`, every group scheme `G` over
`Spec F` whose underlying scheme is affine and whose structure morphism is
locally of finite type, and every cocharacter `χ : Gm → G`. The ambient
rational points are the identity-test points `RationalPoint F G.X` with the
pinned `rationalPointTopology F G.X`. For every supplied topological-group
instance on that topology, the actual subgroup
`(Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec F)))`, with its subspace
topology, satisfies `Langlands.CompactOpenCofinal`: every open subgroup contains
a subgroup that is both compact and open.

The proof specializes
`PointTopology.represented_rationalPoint_subgroup_compactOpenCofinal` to the
published `Dynamic.Affine.centralizerHom χ`. The accompanying published
`isRepresentedBy_centralizerHom` and `isClosedSubgroup_centralizerHom` prove
that its range is the full dynamic centralizer on every test scheme and that
its underlying morphism is a closed immersion. The represented-subgroup
topology theorem supplies closedness in the ambient point topology and
compact-open cofinality from the ambient locally profinite theorem and
Van Dantzig's theorem. The local topology binder is retained explicitly, so
the conclusion concerns exactly the ambient pinned topology and the actual
subgroup topology.

These are internal specializations of existing published constructions by
Worker 115. They add no external-source claim and assume no connectedness,
smoothness or reductivity of either group, no restriction on characteristic,
and no restriction on the cocharacter. The result supplies a topological
input for the dynamic-Levi smooth-dual proof. Admissibility and the closed
`DynamicLeviContragredientFiniteLengthStatement` remain separate obligations.
