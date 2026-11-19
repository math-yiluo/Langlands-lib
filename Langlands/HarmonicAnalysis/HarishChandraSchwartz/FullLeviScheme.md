# The full standard Levi scheme and its norm kernel

This derived structural unit is part of the group-Levi comparison needed for
Waldspurger VIII.4.2, printed p.330 (PDF p.96). It uses the actual standard Levi
scheme and its original inclusion, preserving the distinction between that
chosen representative and the ambient group scheme.

Over any field, for an affine connected reductive group, a maximal split torus
and a generic cocharacter, `rationalFullLeviFunctor_eq_top` applies the published
standard-parabolic endpoint theorem at all simple roots. The result is equality
of subgroup functors on all test schemes. The published represented-subgroup
comparison with the identity then constructs `rationalFullLeviSchemeIso`. Its
forward map is proved to be the original standard Levi inclusion.

Over a nonarchimedean local field, `rationalFullLeviPointHomeomorph` takes points
of this scheme isomorphism. The actual point maps of both scheme morphisms are
continuous for the canonical point topologies. Its forward function is the
point map of the displayed scheme isomorphism.

`mem_rationalCommonNormKernel_fullLevi_iff` preserves the actual norm kernels.
The forward implication applies functoriality of rational-character norms;
the reverse applies it to the inverse scheme morphism. Thus neither norm
family is replaced by an arbitrary family of characters.

This unit supplies no orbit or character Haar normalization, packet estimate,
cuspidality theorem or closed Task 7440 target.
