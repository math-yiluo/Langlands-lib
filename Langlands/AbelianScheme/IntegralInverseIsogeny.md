# Finite étale isogenies from exact integral inverse-multiple data

This internal derived result concerns the actual maps in
`Rationalization.IntegralInverseData A B` for abelian schemes over any base.
If their common integer multiplier is positive and is a unit in the global
sections of the base, both maps are finite étale isogenies. Here isogeny means
finite, flat and surjective, as in `AbelianScheme.IsIsogeny`.

The proof identifies the two composites with multiplication by the positive
natural number represented by the integer. Published invertible-multiplication
results give finiteness, étaleness and surjectivity of those composites.
Separatedness of maps over the base follows from separatedness of the source
abelian schemes. Finiteness then cancels from each composite. Formal
unramifiedness cancels from each composite without further hypotheses, and
étaleness cancels using finite type and formal unramifiedness of the other
factor. Surjectivity of each factor follows from the opposite composite;
étaleness supplies flatness.

No isogeny property of either supplied map is assumed. This result does not
assert that an arbitrary rational isomorphism comes with such data or that a
chosen dual homomorphism is an isogeny without constructing its exact inverse
data. It does not prove a polarization or representability statement.

`finiteEtaleIntegralInverseData` bundles these proved properties with the exact
supplied inverse data. Its underlying data equal the input by reflexivity; in
particular neither integral map nor the multiplier is replaced.
