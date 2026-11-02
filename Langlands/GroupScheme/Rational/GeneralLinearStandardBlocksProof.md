# Block standard subgroups of GL_N

Worker 185, using the simple-root computation of Worker 163.

This derived helper proves the all-test-scheme parabolic, Levi and unipotent
comparisons needed by `GeneralLinearStandardParabolicStatement`. It works over
an arbitrary field and for every natural rank, including zero and one. Only
strict decrease of the chosen cocharacter coordinates is needed.

For a block shape `B`, the published cut correspondence says that two coordinate
indices have the same block label exactly when every cut places them on the same
side. In particular, adjacent indices have the same block label exactly at
an uncut edge. The sign conditions of an actual standard cocharacter, paired
with the adjacent simple characters, say that its integer coordinates agree at
uncut edges and decrease strictly at cuts. The coordinates are therefore
antitone. Equality of coordinates forces every cut to put the two indices on
the same side, since a separating cut would produce a strict inequality.
Conversely, induction along consecutive indices proves equality within one
block. Monotonicity of the published block-label function then identifies the
strict weight order with the reverse strict block order. These arguments cover
the empty and singleton coordinate types without a positive-rank assumption.

The canonical weights `blockShapeWeight B` are the negatives of the block
labels. They have the same equality and strict order relations as every
standard cocharacter. The proof also checks directly that the cocharacter
`cocharacterOfWeights k (blockShapeWeight B)` satisfies all the standard sign
conditions, so the family defining each intersection is inhabited.

Every actual torus cocharacter, composed with the diagonal-torus inclusion,
is the diagonal matrix cocharacter of its coordinate weights. The published
dynamic formulas express parabolic membership by entry vanishing at a strict
weight inequality, Levi membership by vanishing at unequal weights, and
unipotent membership by identity entries at a weak weight inequality. The
weight comparisons therefore identify each of the three dynamic subgroup
functors for every standard cocharacter with the corresponding block functor.
The forward inclusion of each standard intersection uses the canonical
witness; the reverse inclusion uses the comparison for every standard
cocharacter. Equality of subgroup functors is pointwise on every test scheme.

The conventions are those of Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
second edition (2015), Example 2.1.1, printed pp.45–47
(source `conrad-gabber-prasad-2015-pseudo-reductive`, PDF pp.71–73):
decreasing weights give block upper triangular parabolics, block diagonal
centralizers, and identity diagonal blocks for the unipotent subgroup.
Renard, *Représentations des groupes réductifs p-adiques* (2026 French version),
V.3.8, printed p.111
(source `renard-2026-representations-groupes-reductifs-padiques`, PDF p.117),
fixes the minimal-parabolic standardness convention. Renard's setting is a
nonarchimedean local field; the arbitrary-field result here comes from the
published algebraic matrix construction. The positivity and choice-free
intersections used here are derived formulations of these conventions.
