# An open and closed full-level enumeration locus

This internal construction concerns an arbitrary scheme `S`, an actual
abelian scheme `A` over it, and a supplied ordered tuple
`v : SectionTuple A g n`. No dimension equality or numerical torsion-rank
formula is assumed. `fullLevelLocusSet v` consists of base points where
the coefficient sections have no collisions and exhaust the underlying
torsion fibre. At positive order invertible on the base, this subset is
open and closed. `fullLevelLocus` packages it as an actual open subscheme.

The actual torsion morphism is finite and etale. Each coefficient section
is open by unramifiedness and closed by separatedness. The union of their
images is open and closed because there are finitely many coefficients.
The image under the torsion morphism of its complement is also open and
closed. It records fibres with missed points. Collisions between two
coefficient sections are the preimage of one section's image under the
other. These collision loci are open and closed. Removing all distinct
coefficient collisions and fibres with missed points gives the stated
locus. No numerical torsion-rank formula is assumed.

The locus condition gives a bijection on actual kernel morphisms over
every field-valued point whose underlying base point lies in the locus.
Injectivity follows by evaluating at the unique point of the field
spectrum. For surjectivity, coverage puts the underlying point of a
given kernel morphism in one section image. That section is an open
immersion, so the morphism factors through it. Its structure equation
identifies the resulting map to the base with the prescribed base point.
Thus the argument proves equality of morphisms, rather than inferring
it merely from equality on underlying points.

The kernel-point comparison identifies this bijection with the actual
linear-combination map of `fibreTuple v s`. Its inverse gives a basis
whose entries are precisely the supplied ordered entries.
Consequently `isFull_iff_fullLevelLocusSet_eq_univ` identifies the existing
`IsFull v` with the assertion that the locus is the whole base. The
forward implication uses the covering and disjointness already proved
from a supplied full level; the converse uses the recovered fibre bases.

For any actual base change whose underlying image is contained in this
locus, the original fibre bases transport through `levelBaseChangeLinear`.
The published `fibreTuple_pullback` comparison shows that these are
exactly the pulled-back tuple entries. `fullLevelOnLocus` applies this
to the open immersion of `fullLevelLocus` and equips the restricted
abelian scheme with the unchanged notion of ordered full level.

The provenance is internal: the construction combines the published
ordered-tuple, actual-kernel, enumeration and base-change APIs with
`torsionFiniteEtale` and Mathlib's finite-map, open-immersion and clopen-set
geometry. It does not assert that this locus is nonempty, a maximality
equivalence for arbitrary base changes, or existence of a full level on
an arbitrary family. The ordinary moduli space, an embedding and
automorphism rigidity remain separate proof obligations.
