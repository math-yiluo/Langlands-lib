# Original inducing half on the actual coefficient quotient

This is an internal deduction for the rational-point geometric lemma. It moves
the original positive inducing half-character through the actual localized
coefficient quotient. The quotient maps retain every original vector class,
and the comparison is natural and gives an isomorphism of smooth
representations. The full normalized comparison and exact-K0 expansion remain
separate obligations.

For the original standard subgroups P_I, M_I, U_I and P_J, M_J, U_J and a
torus-normalizer point n, use the literal subgroup copies

- S = `(M_J intersect n^-1 U_I n).subgroupOf M_J`;
- Ls = `(M_J intersect n^-1 M_I n).subgroupOf M_J`;
- K = `(M_I intersect n P_J n^-1).subgroupOf M_I`;
- H = `(P_I intersect n P_J n^-1).subgroupOf P_I`.

Let dI and dJ be the original semidirect decompositions. N is the inverse image
in H of the kernel of dI's projection. The coefficient map f is the original
J projection after inverse conjugation from H into P_J. The section from K
into H is the original I Levi inclusion. The homomorphism p is the actual
target-intersection projection followed by inverse conjugation into Ls.
These are the existing maps from `GeometricCoefficientAction` and
`RationalGeometricLocalizedCoefficient`, without replacement subgroup models.

The character chi is exactly
`HaarModulus.closedHalfCharacter U_J hUJ M_J dJ.levi_le_normalizer`.
It is the complex embedding of the canonical positive square root of the
forward Haar modulus of U_J restricted to M_J. No character or choice of
square root is supplied independently.

`isLimitOfCompactSubgroups_geometricSourceIntersection` is a general
topological-group lemma. For any subgroup U that is a limit of compact
subgroups, a closed subgroup M, and any ambient point n, it proves this same
property for `(M intersect n^-1 U n).subgroupOf M`. The proof first uses the
actual conjugation homeomorphism from the conjugate subgroup to U and
`compactLimit_of_closedEmbedding`. The existing closed-intersection lemma
then transports the property into the literal copy inside M. Neither U's
closedness nor local compactness is required for this transport lemma.

For the character results, the ambient rational-point group has a topology,
local compactness and `NonarchimedeanGroup`; the latter supplies the
topological-group structure. U_J and M_J are closed, and U_I is a limit of
compact subgroups. `geometricInducingModulus_eq_one` applies the transport
lemma with U_I and M_J, then the existing
`positiveCharacter_eq_one_on_compactLimit`. The actual restricted U_J Haar
character has open kernel, so its value on every point of S is one.
`geometricInducingHalfCharacter_eq_one` applies the canonical square-root and
complex-unit homomorphisms to this equality.
`geometricSourceRadical_le_ker_inducingHalfCharacter` records S's containment
in the kernel of chi, with S a subgroup of M_J. These results do not require
any root-system hypothesis, source or target intersection decomposition, or
whole-Levi modulus balance.

`geometricInducingHalfSourceCoefficientAction` acts on the original ordinary
Jacquet carrier `Jacquet.Coinvariants sigma S`. It is the action
`(Jacquet.action sigma S Ls hSource.levi_le_normalizer).comp p`, twisted by
`(chi.comp Ls.subtype).comp p`. Thus the half-character is restricted to Ls
and inflated through the actual map p. It is not discarded after proving
triviality on the radical.

`geometricInducingHalfCoefficientEquiv` identifies the actual representation
`geometricLocalizedCoefficientAction ... (twist chi sigma)` with this
source action. Its proof composes the existing
`geometricLocalizedCoefficientEquiv` for `twist chi sigma` with
`Jacquet.actionTwistEquiv`, pulled back along p. The latter uses the proved
kernel containment. The forward and inverse `..._mk` formulas send the
localized class of an original vector v to its ordinary Jacquet class and
back. `geometricInducingHalfCoefficientEquiv_natural` proves compatibility
with the localized map induced by `twistIntertwining chi a` and the ordinary
Jacquet map induced by a, for every original coefficient intertwiner a.
Surjectivity of the original localization quotient reduces this identity to
the representative formulas.

These comparisons retain the structural hypotheses of the actual ordinary
coefficient comparison: an arbitrary field k in universe u, an affine
structural morphism for G, connected reductivity, the original maximal split
torus and generic cocharacter, `StandardCocharacterStatement`,
`HasPointNormalizerComparison`, arbitrary indices I,J of the original
`SimpleRoot` subtype, every actual torus-normalizer point n, and the original
source and target intersection decompositions. Their coefficient field is
complex. Carrier universes uV and uW are independent in naturality. No
characteristic-zero, split-group, minimality, positive-rank, finite-length or
classification premise is added.

With continuity of dJ's original projection, smoothness of sigma implies
smoothness of its twist by chi through
`HaarModulus.isSmooth_twist_closedHalfCharacter_iff`. Applying the existing
smooth localized-action theorem gives
`isSmooth_geometricInducingHalfLocalizedCoefficientAction`. The surjective
actual coefficient equivalence then gives
`isSmooth_geometricInducingHalfSourceCoefficientAction`.
`geometricInducingHalfCoefficientSmoothIso` bundles precisely these two
original carriers as an isomorphism of smooth complex representations. No
smoothness of the source quotient or auxiliary projection is assumed.

The direct proof inputs are compact-subgroup transport, the open kernel of
the actual positive Haar character, the published ordinary localized
coefficient equivalence, the character-twisted Jacquet quotient equivalence,
and smooth restriction and surjective descent. This is an internal
consequence of those existing results, with no new literature translation.
The module imports a larger dependency closure; this account describes the
proof bodies used here. The target inverse half, the intersection Haar
correction, their relation to the normalized source Jacquet functor,
whole-common-Levi distinct-radical balance, the compact/full induction
comparison, the ordered filtration and the unapplied rational geometric K0
expansion are not conclusions of this module.
