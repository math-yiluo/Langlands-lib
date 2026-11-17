# Commutator transfer from source geometry and explicit target word laws

This internal reduction generalizes the published
`LocalSplitWeylCommutatorReduction`. The source has genuine normalized
simple-root data, while the target is an arbitrary group scheme with a
supplied family of additive-group homomorphisms.

`TargetWordRelations` records precisely four kinds of target identities.
Pairs whose roots are nonopposite and have no root in their positive
integral cone must commute. The standard A2 word formula, both B2 formulas,
and all five G2 formulas must hold at the indicated simple-root Cartan
patterns. These are equalities of actual points on every affine test,
using the published `CommRel` convention. The structure supplies no torus,
root subgroup representation, reductivity, affineness, or immersion
property for the target.

The proof follows the implemented published reduction. It derives common
formulas for every pair of distinct positive roots by transporting
standard rank-two formulas along Weyl words. The empty formula treats
commuting cones. A2, the two B2 orientations, and the two G2 orientations
use the same coefficient classification, reversals and ordered-term
arguments as the published proof. Source identities come from genuine
source geometry; target identities come from the four stated fields.
The separate `WeylConjugationRelations` premise supplies the common
rescaling units for the two word families.

An enumeration of positive roots by nondecreasing height converts these
literal formulas into common universal commutator polynomials. The
published source open-cell uniqueness theorem then proves transfer of
every positive-coordinate commutator relation to the target.

`TargetWordCommutatorStatement` states this reduction over every
commutative local ring, and `targetWordCommutator` proves it. No target
root parametrization is assumed. The target word laws and common Weyl
conjugation remain explicit premises; neither their construction for a
powered family nor the affine split isogeny theorem is claimed here.
