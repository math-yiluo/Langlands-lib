# Scalar multiplication and its actual Weil restriction

This derived supporting comparison identifies the dual-number scalar map with
the actual affine Weil restriction of the scalar endomorphism of the additive
line. The base is any field `k` in universe `u`, in arbitrary characteristic;
the scalar is any `c : DualNumber k`.

`VectorGroup.affinePointsEquiv_scalar` first expresses the published scalar
endomorphism in affine algebra coordinates, in any finite vector dimension and
over any commutative base ring. The scalar construction originally uses global
sections on every scheme test. The proof applies
`Corepresented.map_affineSectionsIso_pointsEquiv` to both a point and its scalar
image. The forward algebra isomorphism from sections of an affine test to its
coefficient algebra preserves multiplication and base coefficients, giving the
claimed affine formula.

`restrictedScalar` applies `AffineWeil.map` to `VectorGroup.scalar c` on the
additive line over `DualNumber k`. The tensor comparison sends its base scalar, embedded by
`Algebra.TensorProduct.includeLeftRingHom` (definitionally the original-base
algebra map), to the coefficientwise extension of `c`; this is
`tensorEquiv_includeLeft`. Consequently `affineCoordinates_scalar` reads the
original scalar endomorphism as multiplication by that extended dual number.
The published `groupSchemeMap_points` theorem then gives
`coordinates_restrictedScalar` on every scheme test over `Spec k`, including
nonaffine and nonreduced tests.

The all-test coordinate formula agrees with the earlier `scalarMap`.
Faithfulness of the point functor proves `scalarMap_eq_restrictedScalar`.
Rewriting by that equality gives `restrictedScalarKernelIso`, an actual
group-scheme isomorphism from the scheme-theoretic kernel of the restricted
map to a standard vector group. Its dimension is zero when the constant
coefficient of `c` is nonzero, one when only its epsilon coefficient is
nonzero, and two when `c = 0`. `restrictedScalarKernel_properties` gives
smoothness, connectedness, and the published unipotence predicate for this same
actual kernel.

The provenance is the derived comparison needed to apply the final scalar
calculation in Kaletha–Prasad Lemma C.4.4, printed pp.701–702 / PDF pp.732–733
of the 2023 book, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The source passes from multiplication by a ramified uniformizer power to a
map over the dual-number residue algebra and then restricts scalars. This
module identifies the computed map with the restriction operation itself.
It does not identify an actual ramified special-fibre algebra with the dual
numbers or identify a transition of the unitary models `X_{r,s}` with this
map. Those comparisons and the full C.4.4 and C.5.3 conclusions remain open.
