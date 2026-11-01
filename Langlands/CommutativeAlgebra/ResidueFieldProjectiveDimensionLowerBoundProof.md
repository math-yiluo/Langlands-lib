# The residue-field projective-dimension lower bound

This module proves exactly
`ResidueFieldProjectiveDimensionLowerBoundStatement`, the unconditional lower
bound in Stacks Project Lemma 10.110.3, Tag 00OA. For an arbitrary Noetherian
local commutative ring, the minimal number of generators of its maximal ideal
is at most the categorical, Ext-based projective dimension of its residue
field. Both sides of the inequality use the published statement's conventions.
No finite-projective-dimension assumption is imposed.

The proof follows the Koszul comparison route. Choose lifts of a basis of the
cotangent space, indexed by the maximal ideal's `spanFinrank`. The finite
Koszul modules are functions on subsets of this index set with the prescribed
cardinality. Their differentials square to zero by the independently developed
insertion-sign cancellation construction.

The key detection lemma assumes that a differential lies in the square of the
maximal-ideal multiple. Its coordinates are linear combinations of the chosen
generators. Cotangent independence forces all coefficients into the maximal
ideal. For each source coordinate, erase one index from its nonempty subset;
the corresponding coefficient is the source coordinate times a sign. The
sign's square is one, so the source coordinate itself belongs to the maximal
ideal. The finite-coordinate ideal-multiple lemma gives the required module
membership.

In degree zero, evaluation at the empty subset followed by residue-field
reduction is the augmentation. It annihilates the differential since every
chosen generator lies in the maximal ideal. Its extension of scalars to the
residue field is injective: a degree-zero vector has only the empty coordinate,
and reduction of that coordinate detects membership in the maximal-ideal
multiple. The maximal ideal annihilates the residue field.

The general comparison criterion constructs a comparison to iterated minimal
finite free covers, propagates split injectivity with the detection property,
and bounds projective dimension in every nonzero source degree. Apply it in
the top degree, where the full index set supplies a coordinate and hence a
nonzero free module. This also covers embedding dimension zero. The argument
uses no exactness of the Koszul complex and no regularity criterion or other
conclusions forbidden by the task.

Original source: Stacks Project, [Tag 00OA](https://stacks.math.columbia.edu/tag/00OA),
including the comments correcting the comparison reference and Koszul sign.
The registered complete snapshot is
`stacks-residue-field-projective-dimension-bounds-2026-11-01`.
The implemented insertion convention has the sign given by the number of
smaller indices, which is the usual zero-based deletion-position convention.
