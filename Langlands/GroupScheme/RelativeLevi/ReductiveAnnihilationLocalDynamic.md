# Relative radical annihilation from pointwise dynamic presentations

This internal supporting result concerns arbitrary schemes and universes.
It retains `DynamicRelativeLeviStatement` and pointwise etale dynamic
presentations as explicit hypotheses. It does not prove those hypotheses or
the unconditional `RelativeParabolicReductiveQuotientStatement`.

`RelativeParabolicReductiveAnnihilationLocalDynamicStatement` says the
following. Let `i : P → G` be a relative parabolic subgroup of a reductive
group scheme over a scheme `S`, and let `r : U → P` be a supplied relative
unipotent radical. Assume the dynamic relative Levi theorem in the same
universe. For each point `s` of `S`, assume an etale morphism `b : T → S`,
a point of `T` mapping to `s`, and a cocharacter of the actual pullback of
`G` whose dynamic parabolic is represented by the actual pullback of `i`.
Then every homomorphism `f : P → H` to a reductive group scheme whose
underlying scheme morphism is surjective satisfies `r ≫ f = 0`.
Zero is the trivial group homomorphism, so this is an equation of actual
homomorphisms over `S`.

`RelativeLevi.annihilates_radical_of_pointwise_dynamic` implements the
argument. The relative parabolic predicate supplies affineness of `P`.
On each supplied neighborhood, etale base change preserves the full
relative radical predicate, by
`IsRelativeUnipotentRadical.baseChange_etale`. Arbitrary base change
preserves reductivity of both `G` and `H` and preserves scheme
surjectivity of `f`.

`RelativeLevi.isRepresentedBy_unipotent_of_relativeRadical` uses the
explicit dynamic relative Levi theorem to identify the pulled-back
radical, composed with the pulled-back parabolic inclusion, as a
representative of the ambient contracting subgroup. Applying
`Dynamic.annihilates_contracting_subgroup` therefore makes the pulled-back
composite zero. Finally,
`comp_eq_zero_of_pointwise_etale_baseChange` descends these equalities
from the supplied neighborhoods. It works with actual pullback
homomorphisms and uses fppf subcanonicity; no inference from equality only
on geometric points is made.

`relativeParabolicReductiveAnnihilationLocalDynamic` proves the named
Prop-valued statement using this helper. The neighborhood hypothesis is
the same as that in
`RelativeParabolicReductiveQuotientLocalDynamicStatement`, allowing the
annihilation and quotient-existence results to supply the two inputs of
the universal-quotient reduction. This module itself constructs no
quotient or factorization.

The provenance is internal composition of dynamic annihilation, equality
descent, radical identification, etale radical transport, and reductive
base change. The accompanying prerequisite modules are unchanged
contributions of their respective authors. No additional assertion from
the literature is claimed.
