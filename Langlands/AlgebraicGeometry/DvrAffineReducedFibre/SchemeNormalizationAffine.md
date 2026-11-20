# Comparing scheme and affine normalization

Let `X ≅ Spec D` with `D` reduced and Noetherian, and suppose every
quasi-compact open of `X` has finitely many irreducible components. Then the
normalization in the generic-point residue fields is isomorphic to the
spectrum of the integral closure of `D` in its total fraction ring. The
isomorphism identifies the two normalization maps over the affine presentation.

The proof identifies the maximal ideals of the Artinian total fraction ring
with the minimal primes of `D` and then with the generic points of `X`.
Localization preserves the corresponding residue fields. The Artinian
product decomposition identifies the total fraction ring with the product
of those fields. On spectra this gives an isomorphism from the coproduct of
the generic-point residue spectra. It commutes with the maps to `Spec D`
because each component sends an element of `D` to its residue. The universal
property of relative normalization then gives the desired comparison,
using the affine description of relative normalization.

For a flat `S`-algebra `D` whose generic localization `D ⊗[S] FractionRing S`
is integrally closed in its total fraction ring, the comparison also presents
the scheme normalization as the spectrum of the integral closure in that
generic localization. The file also gives the affine base change chart of
`Spec A` along `Spec S → Spec R` with ring `S ⊗[R] A` and verifies that its
map to `Spec S` is the second pullback projection.

These comparisons are derived from Mathlib's relative normalization and
localization APIs. They connect the normalization in the scheme reduced
fibre premise with the affine normalization that occurs in Conrad's
Theorem A.2.
[Conrad's appendix to Prasad–Yu, p. 28](https://math.stanford.edu/~conrad/papers/qrg.pdf#page=28)
