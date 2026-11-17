# Common Weyl conjugation from source geometry and target identities

This internal derived reduction adapts the published `LocalSplitWeylChains`
height induction to an arbitrary target group scheme. The source retains
its genuine normalized simple-root data over a commutative local ring,
affine structure morphism, and partner uniqueness and inverse rescaling.
The target is supplied only as a family of additive-line homomorphisms
satisfying `TargetWeylRelations`. No target torus, reductivity, affineness,
or root-parametrization hypothesis is used.

The target law bundle contains the alternating-word braid identities, the
source Cartan square signs, fixed conjugation under the two source no-cone
conditions, the A2 and B2 signed map identities, the simple opposite-root
identity, and inverse-unit conjugation of negative roots for every unit.
All are equalities of actual homomorphisms. The negative law retains an
arbitrary unit, rather than restricting the existential unit to a sign.

The source coefficient classifications produce the fixed-law inputs through
the published `noOpp_cone_of_coeffs`. The rank-two-span cases use those
fixed laws and the A2/B2 identities. Outside the span, the published pure
admissible-chain and two-path arguments compare the same two root paths;
target braid equality is their only target input. Strong induction on a
common height bound handles positive roots, using the source and target
square signs when reversing a step. Simple and negative roots are then
assembled using the two explicit target laws and the source geometric
partner results.

`LocalSplitTargetWeylConjugationStatement` states this conditional result in
every universe, and `localSplitTargetWeylConjugation` proves it. The direct
API is `TargetWeylProofs.weylConjugationRelations_of_targetLaws`.

The implementation reuses the published root classifications, numerical
chains and common-unit calculus. Its copied induction wrappers replace
only their target geometric calls with the stated identities. This is a
conditional reduction: proving every target field for the actual powered
family and completing the ambient isogeny construction remain separate
obligations.
