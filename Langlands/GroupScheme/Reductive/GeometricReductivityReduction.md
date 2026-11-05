# Conditional assembly of geometric reductivity

`MatrixRepresentation.separatorOfStructuralInputs` is a noncomputable polynomial
selector for a supplied representation and nonzero fixed vector. It requires all
four hypotheses listed below, as well as pseudo-reductivity of the acting group.
It first selects a positive degree from the conditional assembly and then selects
a polynomial of that degree. Its specification theorem
`MatrixRepresentation.separatorOfStructuralInputs_spec` proves that the selected
polynomial is homogeneous of some positive degree, invariant on every relative
test scheme, and nonzero at the supplied vector. Classical choice supplies the
selection; no computation rule or degree bound is asserted.

`reductiveGeometricReductivity_of_structural_inputs` proves the exact existing
`ReductiveGeometricReductivityStatement.{u}` **conditionally** on these four
propositions, all at the same arbitrary universe `u`:

| Hypothesis | Existing proposition |
| --- | --- |
| `hproduct` | `ReductiveCentralDerivedProductStatement` |
| `hcover` | `SimplyConnectedDerivedCoverExistenceStatement` |
| `hmap` | `SimplyConnectedPositiveCharConjugationMapStatement` |
| `hzero` | `ReductiveCharZeroSemisimplicityStatement` |

This module does not prove any of these four propositions. In particular, its
conditional theorem is not an unconditional proof of Haboush's theorem. It
changes none of the target's definitions or quantifiers.

The content is an internal composition of existing Library constructions. Its
provenance is the determinant construction, flat-surjective descent of invariant
polynomials, the central zero-weight projection and product criterion, the
normalized finite regular-map construction and intertwiner pullback, actual
subgroup representability and central-isogeny transport, the proved finite
Galois splitting of tori, and the conditional characteristic-zero degree-one
separator. No new external source assertion is used in this composition.

`HaboushReduction.separator_of_simplyConnected_cover` works over an algebraically
closed field of a supplied prime characteristic `p`. It pulls the representation
and its nonzero fixed vector back along a supplied central isogeny from a simply
connected group. Applying `hmap` gives a conjugation-equivariant linear map whose
value is a nonzero scalar identity matrix of positive size. Its determinant is
a homogeneous invariant of positive degree with nonzero evaluation. The central
isogeny is flat and surjective, so the existing restriction equivalence descends
polynomial invariance to its target. The auxiliary representation stays on the
cover; the proof does not assert that it descends.

`HaboushReduction.separator_of_central_split_product` applies this construction
to the restriction to the supplied covered factor. A supplied central split
torus has a zero-weight projection, which fixes the given fixed vector. Pullback
through the projection preserves the separator's homogeneous degree and
nonzero value, and gives torus invariance while preserving invariance under the
other factor. The existing epimorphic subgroup-product criterion then gives
full-group invariance. The acting group and the covered factor are affine, and
the product epimorphism is explicit.

`HaboushReduction.epi_subgroupProductMap_iso` proves that reparametrizing one
factor by a group-scheme isomorphism preserves that product epimorphism: the new
product map is the old one precomposed with the product of the underlying
isomorphism and the identity. No stability of arbitrary epimorphisms under base
change is assumed.

`HaboushReduction.separator_fin_of_structural_inputs` obtains the central torus
and actual derived subgroup from `hproduct`, and a simply connected cover of an
actual derived subgroup from `hcover`. Representability identifies the two
actual derived subgroups. Postcomposing the cover with this isomorphism preserves
its central-isogeny properties. The derived subgroup is affine because it is
closed in the affine ambient group. The proved finite Galois splitting theorem
makes the central torus split over the algebraically closed field; transporting
its inclusion preserves centrality and the product epimorphism. The preceding
split-product construction then gives a separator for any representation on
`Fin N`. Derived semisimplicity is not an additional assumption: the supplied
simply connected cover includes its required semisimple source.

`HaboushReduction.separator_of_structural_inputs` passes from arbitrary small
finite coordinate types to standard finite coordinates using the normalized
finite regular-map construction. It provides an actual intertwiner sending the
given vector to a vector whose basis expansion is the constant function one.
This image is nonzero: equality to zero would give `0 = 1` in the actual
coordinate algebra and, under its counit, in the field. The standard-coordinate
separator pulls back through this intertwiner with the same positive degree
and nonzero value. No injectivity of the intertwiner is required.

The final theorem splits according to the characteristic of the field. Prime
characteristic uses the preceding conditional construction; characteristic zero
uses the existing conditional degree-one consumer of `hzero`. All polynomial
invariants and fixed-vector conditions throughout use the unchanged Library
predicates on every relative test scheme, without affine or reduced restrictions
on those tests. The field universe is arbitrary, and coordinate types have the
same small finite universe as the original target.
