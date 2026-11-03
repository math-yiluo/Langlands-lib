# Geometric unipotent radicals and rational Levis in affine groups

Author: Worker 1355.

This is an internal consequence of the published radical comparison,
`IsUnipotent.baseChange`, represented dynamic subgroup transport, and the
actual scheme multiplication isomorphism. It asserts no new external
structure theorem. All declarations are general in the field universe `u`.

For a morphism `r : U → P` with affine ambient group scheme `P`,
`IsGeometricUnipotentRadical.isUnipotentRadical` proves the ground-field
radical predicate from the semistandard geometric radical predicate.
`IsGeometricUnipotentRadical.leviSubgroup` upgrades that same input to
`LeviSubgroup.IsGeometricUnipotentRadical r`, which requires the radical
predicate over both the ground field and its algebraic closure. The proofs
instantiate the existing conditional comparison with the published theorem
that unipotence of an affine group scheme is preserved under arbitrary
same-universe field extension. Its stronger theorem does not need the
finite-type premise allowed by the conditional comparison. No unproved
unipotence preservation premise remains in these declarations.

`leviSubgroup_isGeometricUnipotentRadical_iff_of_affine` combines the upgrade
with the existing converse. `LeviSubgroup.geometricUnipotentRadicalEquivOfAffine`
packages this equivalence of propositions as an equivalence of their proof
types. The existing conditional comparison remains unchanged.

`IsRationalLeviSubgroup.of_geometricUnipotentRadical` constructs the rational
Levi predicate from a closed morphism `l : L → P` with connected reductive
source, a supplied semistandard geometric unipotent radical `r : U → P`,
and the hypothesis that the actual scheme morphism
`subgroupMultiplication l r : L.X ⊗ U.X → P.X` is an isomorphism over the
base field. It upgrades the supplied radical and records these witnesses
in the rational Levi structure. Affineness of `P` remains a hypothesis.

`Dynamic.isRationalLeviSubgroup_of_geometricUnipotentRadical` applies this
constructor to actual representatives of a dynamic parabolic, centralizer
and unipotent subgroup of an affine separated group scheme `G`, for a
cocharacter `χ`. Given compatible maps `l : Z → P` and `r : U → P`, it
still requires connected reductivity of `Z` and the geometric unipotent
radical predicate for `r`. Closedness of the parabolic and centralizer
representatives follows from the published affine representative transport.
The former gives affineness of `P`, and cancellation of closed immersions
gives closedness of `l`. The published
`Dynamic.isIso_subgroupMultiplication` supplies the actual Levi-first
multiplication isomorphism. Thus the conclusion contains a scheme
isomorphism, together with the full ground-field and geometric radical
greatestness, rather than only a factorization on field points.

The constructors require the stated actual reductivity and radical data.
They prove no existence of those data or of a cocharacter for an arbitrary
parabolic, no solvable radical existence or torus intersection theorem,
and no instance of the full adapted rational Levi statement.
