# Root-datum morphisms from explicit geometric comparisons

This internal construction combines the Library's actual lattice maps, adjoint
weight spaces, normalizer actions and isomorphism criteria. It adds no external
literature claim. The field has arbitrary universe, and the two supplied root
index types have independent universes.

Let `G` and `G'` be affine group schemes locally of finite type over any field
`k`. Let `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G'` be closed inclusions of split
tori, and let `φ` be a central isogeny. The construction retains these explicit
geometric inputs:

- a commuting square with `t : T ⟶ T'` and an isogeny on the underlying group
  schemes of the tori;
- equality of each all-test-scheme torus centralizer with the actual pointwise
  range of its inclusion;
- `Lie.dimension G = Lie.dimension G'`;
- finiteness of the full target normalizer image `weylImage i'` on its entire
  integral character lattice.

`IsCentralIsogeny.roots_bijOn_of_comparisons` derives the actual root pullback
bijection. Flat surjectivity of the torus isogeny gives an epimorphism of
schemes, so actual character pullback is injective. The explicit
self-centralizer equalities and the split-torus isogeny give the required
zero-weight dimension equality through
`Lie.finrank_zeroWeight_eq_comp_of_torus_isogeny`. The ambient dimension equality
then supplies the other input of
`roots_comp_eq_of_central_kernel_of_dimensions`. This compares root supports
for two actions of the same source torus. `roots_bijOn_of_comp_eq` converts it
into the root bijection between the two actual tori.

For any supplied root data `P` and `P'` satisfying `IsRootDatumOf`,
`IsCentralIsogeny.rootDatumHomOfComparisons` constructs `RootPairing.Hom P' P`.
The root ranges of the supplied data equal the actual root sets, so the
preceding bijection gives the index equivalence. Scheme epimorphy of `t`
also gives epimorphy of its underlying group-scheme homomorphism. The
published `IsRootDatumOf.coroot_comp_of_finite_weylImage` then identifies
the pushforward of each source coroot with the matched supplied target
coroot. This uses the finite full normalizer action, including its action
in central character directions. `RootDatumHom.ofRootCoroot` assembles
these data, with the actual lattice pairing checking transposition.

`IsCentralIsogeny.rootDatumHomOfComparisons_spec` assumes that the source
torus is maximal and proves all five conclusion clauses:

- the weight map is actual character pullback `χ ↦ t ≫ χ`;
- the coweight map is actual postcomposition `ν ↦ ν ≫ t`;
- the weight map is injective by scheme epimorphy of the torus isogeny;
- the coweight map is injective by finiteness of the ambient isogeny and
  its restriction between closed inclusions;
- `φ` is an isomorphism exactly when this weight map is bijective.

For the last clause, maximality of the source torus gives invertibility of
the restriction when the ambient map is invertible. Conversely, the full
central kernel lies in the source torus by its supplied self-centralizer
equality. An invertible restriction makes that kernel trivial, and a finite
flat surjective monomorphism is an isomorphism. The split-torus character
isomorphism criterion identifies invertibility of the restriction with
bijectivity of actual character pullback.

The map identities are definitional. No step assumes separability,
perfection, a characteristic restriction, or smoothness of an isogeny or
its kernel. The four geometric inputs above remain premises. In particular,
this module does not prove `CentralIsogenyRootDatumHomStatement`; proving
those inputs in its complete reductive setting remains necessary.
