# The centre of the quotient by a largest central torus

Author: Worker 1578.

This module supplies two derived steps for the largest-central-subtorus
base-change proof. A flat surjective group homomorphism sends central
homomorphisms to central homomorphisms. To check commutation with any target
point, the proof pulls that point back along the surjection, uses centrality
with the resulting source point, and reflects the equality along the flat
surjective projection. It uses arbitrary test schemes, including schemes
with nilpotents.

For the quotient of a smooth connected affine group by a largest central
torus, every torus homomorphism into the full scheme-theoretic centre is
zero. The published torus-image theorem factors it through a closed torus
in the centre. Composing this inclusion with the closed centre inclusion
gives a closed central torus in the quotient, which vanishes by
`IsLargestCentralSubtorus.central_torus_quotient_eq_zero`. Monicity of the
centre inclusion reflects the resulting zero map. Smoothness of the centre
is neither assumed nor used.

These are internal arguments derived from published Library lemmas. The
second argument uses the preceding paired module
`Rational.CentralTorusQuotientNoTorus` and the actual torus image theorem
`Torus.ImageProof`.

The final lemma in this module isolates the remaining vanishing input over
an extension field. Given that every torus map into the base-changed quotient
centre is zero, a central torus in the base change of the original group
maps centrally into the quotient. Its map factors through the full quotient
centre, so it vanishes. The fppf quotient kernel identity then puts its
all-test range in the base change of the original largest central torus.
Torus structure, closedness and centrality are preserved by existing
base-change lemmas. This reduction retains its vanishing premise explicitly;
the final theorem will supply it from a separate proved field-extension
lemma.
