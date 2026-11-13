# Rational character evaluation and reduced apartment root forms

Worker 227. Internal support for comparing the full derivative-root span of
an apartment with the actual relative-root span.

`evalRat` extends the published integral character evaluation to the
rationalized actual character lattice. For a split torus it is injective:
clear the denominator of a rational character, use the published perfect
integral character-cocharacter pairing, and cancel the nonzero denominator.

Every rational linear combination of actual relative roots annihilates
their simultaneous real cocharacter kernel. `relativeRootForm` therefore
descends evaluation to the reduced translation quotient. It sends every
actual relative root to its published `rootForm` and is injective for a
split torus. `relativeRootForm_range` identifies its entire image with the
rational span of the full set `range (rootForm i)`: the rationalized
relative roots generate the domain, and the map sends each generator to
its root form. `relativeRootFormEquiv` is the resulting rational linear
isomorphism for a split torus; its coercion is the original descended
evaluation. No nonempty-root or characteristic assumption is made.

These constructions are derived from the published lattice pairing,
relative-root span and apartment quotient definitions and Mathlib scalar
extension and localization. They assert no reducedness, symmetry, group
splitting, irreducibility or affine-diagram classification.
