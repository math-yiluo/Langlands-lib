# Geometric radicals and actual finite Galois torus-quotient descent

Worker 1333.

This internal construction recognizes geometric unipotent radicals from
actual torus quotients, and descends a supplied torus quotient over a finite
Galois extension. All fields and characteristics are retained, at the
original universe. It does not construct the initial extension-field torus
quotient or prove split unipotence of its kernel.

`IsUnipotentRadical.of_torus_quotient` assumes an affine ambient group, a
closed smooth connected unipotent subgroup, and an actual represented fppf
quotient by its full kernel whose target is a torus. Normality follows from
the full kernel equality. For every candidate normal unipotent subgroup,
its source is affine because its inclusion in the affine ambient group is
closed. The published unipotent-to-torus vanishing theorem kills its
composite with the quotient. The full kernel equality therefore gives
containment on every scheme test, proving the radical's greatestness.

`LeviSubgroup.IsGeometricUnipotentRadical.of_torus_quotient` applies the same
argument over the algebraic closure. Closedness, smoothness, connectedness
of the affine smooth group, unipotence, the torus property, and the full
fppf kernel quotient persist after this field extension by published
Library results. Thus geometric greatestness requires no separate premise.

`FiniteGaloisTorusQuotientDescent i q` retains an actual ground-field
radical and its inclusion, an isomorphism recovering the supplied kernel
source over the extension, and the exact commuting inclusion equation.
It also retains the published `SmoothNormalQuotient` data for this same
ground-field inclusion, the torus property of that same quotient target,
an isomorphism recovering the supplied quotient target, and the exact
commuting projection equation. The radical satisfies the unchanged
`LeviSubgroup.IsGeometricUnipotentRadical` predicate.

`finiteGaloisTorusQuotientDescent` assumes the ground-field ambient group
is smooth and affine and is given an actual finite Galois extension and
torus quotient of its base change. Its supplied full kernel must be
closed, smooth, connected and unipotent. The recognition theorem first
makes that inclusion a represented radical. The published
`IsUnipotentRadical.finiteGaloisRadical` descends the actual inclusion,
retaining its source comparison isomorphism. The published smooth normal
quotient constructor produces an actual quotient over the ground field.
Its base change has the same full kernel as the supplied torus quotient,
using the inclusion equation and invariance of the represented range under
a source isomorphism. Both projections are quasi-compact: this is stored
by the smooth quotient data and preserved by base change for the first,
and follows from affineness of the source and torus target for the second.
`FppfQuotientComparison.iso` identifies the actual quotient targets and its
factorization theorem supplies their projection equation. The existing
torus reflection theorem makes the ground-field quotient a torus.
Recognition then proves that its actual kernel is a geometric radical.

The provenance is entirely internal: these constructions compose the
published vanishing, field-extension, represented radical descent and
quotient comparison results. No absolute solvable torus-quotient theorem,
solvability, torus-generatedness, or connectedness of the ambient group
is assumed. Obtaining the initial finite Galois quotient and proving
splitness of the resulting radical remain prerequisites for the full
rational maximal-torus conjugacy theorem.
