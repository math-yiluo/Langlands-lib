# Prescribed extension-field models in actual component covers

This derived internal construction keeps an explicitly supplied finite
separable extension `E/k`, actual affine simply connected absolutely
almost-simple group `H/E`, and Weil presentation of a specified almost-simple
product factor. It avoids choosing a different existential Weil model when
the geometric comparison has already fixed the field and group.

`FactorComplement` and `factorComplement` give an actual simply connected
complement to the original product factor. The product isomorphism retains
the original insertion. The proof uses the arbitrary-field normal-complement
theorem, simple connectedness to upgrade its central-isogeny multiplication
to an isomorphism, and reflection of simple connectedness to a direct factor.

`weilFactorOfIso` substitutes the supplied Weil presentation in the left
coordinate of that isomorphism. Its extension and factor are definitionally
the prescribed `E` and `H`, as stated by the two projection lemmas. The actual
cover, its full scheme-theoretic centrality, original insertion and anisotropy
comparison are the existing `SimplyConnectedWeilFactor` interfaces.

`SimplyConnectedWeilFactor.componentFactor` assembles the complete original
`TitsIndexData.ComponentFactor` from these actual group data and a supplied
actual index on `H`, an equivalence with the entire prescribed component,
every ordered Cartan equality and the two simultaneous full-star image lifts.
The group cover and anisotropy clauses follow from the existing actual
cover construction and split-rank comparison. The Cartan and star comparisons
remain explicit premises; no unconditional component-realization result is
claimed in this assembly unit.
