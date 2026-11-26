# Cuspidality from the proper standard constant terms

`standardParabolicFamily_range_top` identifies the full standard parabolic
with the ambient group at the level of subgroup functors.
`hasCuspidalConstantTerms_of_standard` proves that a continuous
left rational-invariant adelic function is cuspidal if its actual constant
term along each proper standard parabolic vanishes.

The dynamic presentation and the rational classification conjugate an
arbitrary parabolic to a member of the standard family. The full index
cannot occur for a proper parabolic. The resulting isomorphism of
parabolics carries the geometric unipotent radical to the standard radical
because the unipotent radical is unique as a subgroup functor. This
identifies the two radical subgroups in the ambient group up to rational
conjugacy. Transport of the normalized quotient measure under that
conjugacy and rational left invariance then transport vanishing of the
constant term.

The result is derived from the rational parabolic classification in
`StandardParabolicClassificationProof` and the normalized constant-term
covariance in `GroupSchemeConstantTermConjugation`.
