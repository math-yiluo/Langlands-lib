# Actual root-weight lines from triviality of scheme line bundles

This internal construction supplies the affine root-line freeness step
needed for the isomorphism and `G(S)`-conjugacy of reductive groups with
split maximal tori and Borel subgroups over a connected base with trivial
Picard group. Its Picard hypothesis is precisely triviality of
all actual `LineBundle (Spec R)` objects, as in the published parent
statement. No module Picard hypothesis is substituted for it.

For the group-scheme conclusions, let `R` be an arbitrary commutative
ring, let `G` be a reductive group scheme over `Spec R`, and let
`i : splitTorus (Spec R) I ⟶ G` be a finite coordinate split torus
that is fibrewise maximal. Supply a full fibrewise root datum `P` for
this map. Reductivity and fibrewise maximality are separate hypotheses;
they are not consequences of the supplied root datum.

For a finite projective module of rank one at every prime,
`isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one` proves that its actual
associated sheaf is a line bundle. The published principal-localization
trivialization theorem gives a free line on a principal neighbourhood of
each prime. The actual tilde pullback comparison turns this module
trivialization into a trivialization of the restricted associated sheaf;
restriction compatibility of the rank-one locus gives the required
neighbourhood on the original spectrum.

`nonempty_linearEquiv_of_lineBundlesTrivial_of_rankAtStalk_eq_one` applies
the given line-bundle triviality to this actual associated sheaf and
uses full faithfulness of the tilde functor to recover a linear
equivalence with the original coordinate ring. This includes the empty
spectrum case and adds no nontrivial-ring assumption.

Under these group-scheme hypotheses, `rootWeightRank_eq_one` applies the
published field root-Lie-line theorem to the actual residue-field fibre
at each base prime. Reductivity gives a connected reductive fibre and
fibrewise maximality gives a maximal torus on that actual fibre. The
supplied full fibrewise root datum identifies its root character as an actual root.
The actual weight-space base-change dimension comparison gives rank one
for the original finite projective root-weight module at that prime.

`rootWeightSpace_nonempty_linearEquiv_of_lineBundlesTrivial` combines
these constructions under the same reductivity, fibrewise maximality
and full fibrewise root-datum hypotheses, together with triviality of
every actual `LineBundle (Spec R)`. It trivializes every actual root
summand over the original ring without a local-ring or connectedness
assumption. The input finite projectivity,
field root-line theorem, actual base-change comparisons and associated
sheaf constructions are all published results imported by Lean name.

`rootWeightSpaceEquivOfLineBundlesTrivial` is the noncomputable,
noncanonical choice of the linear equivalence from the actual root-weight
module to `R` supplied by the preceding existence theorem. It has exactly
the same actual-line-bundle Picard, reductivity, fibrewise maximality and
full fibrewise root-datum hypotheses.
