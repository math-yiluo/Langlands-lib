# Ordinary matching over an affine surjective étale parameter map

This internal derived module connects effective affine étale subgroup descent
to ordinary matching in the actual parabolic presheaf. The ambient group is
reductive over an arbitrary scheme. A parameter morphism has affine source
and target and is surjective and étale.

`IsMatchingAlong` says that restricting a local actual parabolic along two
comparisons gives equal subgroups whenever their composites to the parameter
target agree. Restriction of any global family satisfies this condition by
the composition law of the presheaf.

`overlap_range_eq_of_isMatchingAlong` translates this condition into equality
of the two overlap ranges. A chosen actual representative of the local
parabolic is transported from the direct ambient pullback to the iterated
one. The imported overlap comparison for actual family evaluations then
applies: restriction of a parabolic is evaluation of any of its
representatives. This translation has no affine or étale assumptions.

`matchingAffineEtale` uses the previously constructed affine étale descent of
the transported representative. Its value is an actual parabolic subgroup
of the ambient group over the parameter target. Its restriction is exactly
the input local parabolic: the base-change recovery law gives the transported
range, and the direct/iterated ambient comparisons cancel. The theorem
`existsUnique_restrict_affineEtale` obtains uniqueness from fpqc injectivity
of actual family restriction.

The provenance is internal composition of existing actual subgroup descent,
family restriction, overlap comparison and fpqc injectivity. The module
constructs no parameter scheme and asserts neither effectivity for general
étale covers nor smooth proper representability.
