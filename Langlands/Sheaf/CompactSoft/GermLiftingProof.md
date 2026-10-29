# Compact-germ lifting with a c-soft kernel

Author: Worker 1007. Coauthor: Worker 310, whose shared parent-task draft
supplied the explicit additive and finite-limit-preserving evaluation setup.

The theorem `Langlands.Sheaf.CompactSoft.compactGermLifting.{u}` proves exactly
`Langlands.Sheaf.CompactSoft.CompactGermLiftingStatement.{u}`. It quantifies over
a locally compact Hausdorff `X : TopCat.{u}`, a commutative ring `R : Type u`,
and a short exact complex `S` of sheaves of `ModuleCat.{u} R`. If `S.X₁` is
c-soft, every germ of `S.X₃` along a compact subset lifts to a germ of `S.X₂`.
There is no additional hypothesis on the space or complex.

## Implemented proof

`HasNeighbourhoodLift S s K` is an internal proposition: for a quotient
section `s` on an open set `O`, there exist an open neighbourhood `V` of `K`,
an inclusion `V ⟶ O`, and a middle-sheaf section on `V` whose image is the
restriction of `s`. This is a stronger intermediate conclusion for a fixed
representative of the quotient germ. The definition does not assert that lifts
exist; the following lemmas construct them.

The elementary helpers `restrict_restrict` and `map_restrict` express
composition of restrictions and naturality on elements. `map_kernel_zero`
expresses the short complex's zero composite on sections.
`exists_kernel_section` uses the functor from sheaves to modules obtained by
forgetting to a presheaf and evaluating on an open set. This functor is additive
and preserves finite limits. Applying its exactness-and-monomorphism
characterization to the short exact complex, followed by the elementwise
criterion for exact complexes of modules, lifts any section with zero quotient
image to a kernel section on that same open set.

`exists_glue_pair` and `section_ext_pair` use the sheaf's pullback cone for two
opens. An element of a module is encoded by the linear map from `R` sending
`1` to that element; the pullback's lifting and uniqueness properties then give
binary section gluing and uniqueness. `section_ext_empty` uses the terminal
value of a sheaf on the empty open set. Consequently a quotient section admits
a lift near the empty subset (`HasNeighbourhoodLift.empty`), using the zero
section on the empty open set. `HasNeighbourhoodLift.mono` retains a lift when
the subset is made smaller.

`exists_compact_overlap_shrink` provides the necessary topological shrinking.
For compact `A` and `B` inside representing opens `U` and `V`, and an open
neighbourhood `W` of `A ∩ B`, the compact sets `A \ W` and `B \ W` are
disjoint. Hausdorff separation of these compact sets gives disjoint open
neighbourhoods `P` and `Q`. The opens
`U' = U ∩ (W ∪ P)` and `V' = V ∩ (W ∪ Q)` contain `A` and `B`, respectively,
are contained in the original opens, and satisfy `U' ∩ V' ⊆ W`.

The main gluing lemma is `HasNeighbourhoodLift.union`. Suppose `a` and `b`
lift the same quotient section near compact `A` and `B`. Their difference on
the open overlap has zero quotient image. `exists_kernel_section` lifts that
difference to a section `c` of `S.X₁` there. The intersection `A ∩ B` is
compact, so c-softness extends the germ of `c` along this intersection to a
global kernel section `c'`. Only the extension property is needed in this
step; the resulting compact support is not used further.

The published `setGerm_eq` gives an open neighbourhood `W` of `A ∩ B` on
which the restrictions of `c'` and `c` agree. Subtracting the image of `c'`
from `a` preserves its quotient image and makes it equal to `b` on `W`.
The shrinking lemma then produces smaller neighbourhoods with overlap inside
`W`. The corrected sections agree on that actual overlap and glue by
`exists_glue_pair`. Their quotient image is the restriction of the original
section, by `section_ext_pair`. Thus the result lifts near `A ∪ B`.
`HasNeighbourhoodLift.finset_union` repeats this construction by induction on
a finite family of compact sets, starting with the empty case.

`exists_lift_near_compact` uses local surjectivity of the epimorphism `S.g`.
At each point of `K`, a local lift exists on an open subset of `O`.
Local compactness and regularity (the latter follows from local compactness
and Hausdorffness) give a smaller open neighbourhood whose compact closure
lies inside that lifting domain. The interiors of these compact closures cover
`K`. Compactness selects finitely many of them, the finite-union lemma gives a
lift near their union, and monotonicity gives a lift near `K`.

Finally, `compactGermLifting` represents a quotient germ using
`exists_setGerm_eq`, applies `exists_lift_near_compact` to that representative,
and takes the resulting middle-sheaf germ. Naturality of `setGerm` and its
compatibility with restriction show that its image is the original germ.

## Provenance and scope

This is the derived compact-germ intermediate lemma in the finite-cover proof
of Kashiwara–Schapira, *Sheaves on Manifolds* (1990), §2.5, Proposition 2.5.8,
printed p.105. It is not a separately named proposition in the source.
Proposition 2.5.1(ii), printed pp.102–103, supplies the compact colimit-germ
interpretation. Definition 2.5.5 and Proposition 2.5.6, printed pp.104–105,
explain the c-soft extension convention used by the published `IsCSoft`.
The proof uses that existing definition and the existing germ API directly;
no new comparison with alternative definitions is claimed. The shrinking,
open exactness and finite gluing lemmas are the explicitly implemented
intermediate steps of this derived argument.

The conclusion concerns germs along compact subsets. Compact-support lifting
in the middle sheaf and the final compact-support exactness theorem belong to
the separate parent task.

Registered source:
`provided-1a1e547af2f3cfc223f73a05ef9491bbf82f0d1976763c0d9c200813c4b8b658`;
file `literature/Kashiwara, Schapira - Sheaves on Manifolds, Grundlehren 292 (1990).pdf`;
SHA-256 `27c80b305bf07611948cc4ebb154c9abae7454f1eed67cbe10cfb0318f0c2163`.
Worker 1007 read one-based PDF pages 112–115 and visually checked page 115
(printed p.105). No source-specific errata note was present in public notes
when the source was read.
