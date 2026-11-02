# Positive real ideles

This construction uses the actual adele ring of an arbitrary number field `F`.
`PositiveRealIdeles.full` is a continuous multiplicative map from the units of
the nonnegative reals to `Ideles F`. Each infinite component is the same positive
real in the real subfield of its completion; every finite component equals one.
The map is injective.

The source is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*
(1995), Chapter I, §2.1, printed pages 18–20, registered as
`moeglin-waldspurger-1995-spectral-decomposition`. The passage defines the
positive-real archimedean subgroup used to realize split tori. This module
constructs its scalar idele map only. It does not construct a torus in a
reductive group, choose simple roots, define a Siegel set, or assert reduction
theory or finite volume.

`realEmbedding` uses Mathlib's inverse real completion isomorphism at a real
place and the inverse complex completion isomorphism composed with the usual
real inclusion at a complex place. Its image under the chosen extended complex
embedding is precisely the original real number. The inverse isometries prove
continuity, and the extended embedding isometry proves that the local norm is
the ordinary real absolute value. `infiniteRealEmbedding` takes the product of
these maps. Applying the units functor to its restriction to nonnegative reals
gives `infinite`; the existing inclusion with finite part one gives `full`.
Injectivity follows by evaluating at any infinite place.

The normalized idelic absolute value of `full F x` is
`x ^ Module.finrank ℚ F`. This retains Mathlib's multiplicity one at real places
and two at complex places: the product of the local powers is the power by the
sum of these multiplicities, which is the degree of `F`. No degree normalization
or rescaling is hidden in the embedding.
