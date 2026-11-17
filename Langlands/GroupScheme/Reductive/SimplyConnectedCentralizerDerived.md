# Simply connected derived groups of relative split-torus centralizers

Worker 634.

This internal construction provides actual subgroup schemes for a possible
simple-factor construction over an affine base. Let `G` be reductive over
`Spec R`, with simply connected geometric fibres, and let `a : T → G` be a
closed split subtorus. `SplitTorusCentralizerDerivedModel a` retains an actual
centralizer `C → G`, a relative derived subgroup `D → C`, reductivity of both,
and simple connectedness of all geometric fibres of `D`. The composite
`D → C → G` is a closed subgroup. No assertion that `D` is almost simple,
normal in `G`, or a factor of `G` is made here.

The centralizer is obtained from the published smooth closed representability
of split-torus centralizers over arbitrary commutative rings. Its reductivity
is checked on the actual geometric fibres: a generic cocharacter of the split
torus has the same centralizer, and the published dynamic-centralizer theorem
gives connected reductivity on each field fibre. The relative derived-group
existence theorem, supplied with the published relative semisimple
fppf-perfectness proof, then constructs `D`.

For any admissible relative derived subgroup of the chosen centralizer,
the published torus-quotient criterion identifies its pullback to every actual
field-valued point with the scheme-theoretic derived subgroup there. The
published field theorem for derived groups of split-torus centralizers gives
simple connectedness on each geometric fibre. The model also exposes this
exact derived-subgroup property on arbitrary specified field-valued fibres.

These are derived consequences of published Library constructions. The
motivating source is Brian Conrad, *Reductive group schemes* (2014), registered
as `conrad-2014-reductive-group-schemes`, Proposition 6.4.4 and its proof,
pp.232–233: the proof recovers simple factors as derived groups of centralizers
of complementary tori. This module implements the relative construction and
its simply connectedness property; it does not implement the complementary
torus selection, almost simplicity, product isomorphism, or Weil descent.
