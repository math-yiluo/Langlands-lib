# Smooth moduli of actual closed torus subgroups

Author: Worker 1656.

`TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement.{u}`
is an existence proposition for every actual smooth affine group scheme
`G/S`, where `S : Scheme.{u}` is arbitrary. It asks for an actual scheme
`M/S`, an actual group scheme `K/M`, and an actual homomorphism
`j : K ⟶ G_M`. The map `j` must be a closed subgroup inclusion, its source
must satisfy `RelativeTorus.IsTorus`, and `M → S` must be smooth.

The remaining conjunct is the actual-family condition
`TorusSubgroupModuli.IsUniversal j`. For every scheme `T/S` and every
subgroup functor of `G_T` represented by an actual closed relative torus,
it requires a unique actual morphism `a : T ⟶ M` whose evaluated range is
that subgroup functor. Evaluation uses the pulled-back inclusion and
`Descent.pullbackComparison` from the imported interface. The equality
therefore concerns the literal ranges on all schemes over `T`, including
nonaffine and nonreduced tests. The separate closedness and torus
conjuncts ensure that every evaluation is itself admissible, by
`TorusSubgroupModuli.isAdmissible_evaluate`.

No restrictions on reducedness, Noetherian hypotheses, connectedness of
the ambient fibres, or a globally constant torus rank are imposed.
The relative-torus predicate permits a different finite rank on each
member of a jointly surjective étale cover, including rank zero.
The statement asks for smoothness of `M/S`, without requiring `M/S` to
be affine or quasi-compact or asserting separatedness.

This is a derived torus specialization of SGA 3, Exposé XI, Theorem 4.1,
which represents multiplicative-type subgroups of a smooth affine group
by a smooth separated scheme. The theorem is on PDF page 20,
recomposed page 104, original page 157, of `Expo11.pdf` in the registered
Gille–Polo provisional recomposition of 5 December 2008, source
`sga3-exposes-xi-xii-xiv-gille-polo-2008`. The original theorem is broader
than the present torus target.

The specialization is justified at the level of mathematical statements
as follows. Exposé IX, Definition 1.3, identifies tori with groups
fpqc-locally isomorphic to finite products of the multiplicative group;
the rendered PDF page 2 explicitly allows nonnegative rank. Remark 1.4.1
on PDF page 3 says the character type of a multiplicative-type group is
locally constant. Apply this to the universal subgroup in XI 4.1:
the union of the components whose character type is a finite free
abelian group is open and closed. Restricting the universal subgroup to
that locus gives the torus subfunctor and preserves smoothness.
Exposé X, Corollary 4.5, PDF page 17, recomposed page 79, original
page 97, supplies étale splitting of finite-type multiplicative-type
groups. Along with IX 1.3 and 1.4.1, it identifies this torus condition
with the étale splitting condition used by `RelativeTorus.IsTorus`.
Closed subgroup schemes of the finite-type affine ambient group are of
finite type, so this splitting result applies.

The IX and X citations use the registered Gille–Polo recompositions of
8 November 2009, sources `sga3-expose-ix-gille-polo-2009` and
`sga3-expose-x-gille-polo-2009`. No source-specific errata files for these
three sources were present in the consulted Library.

The Lean module only defines this proposition. It proves neither the
subgroup-moduli theorem nor the comparisons and restriction construction
just described. A proof of the proposition must construct the actual
universal family and establish its all-test evaluation property from
the stated hypotheses. The intended application is the graph
construction for smooth representability of Hom from a split torus;
that Hom theorem is a further obligation and is not asserted here.
