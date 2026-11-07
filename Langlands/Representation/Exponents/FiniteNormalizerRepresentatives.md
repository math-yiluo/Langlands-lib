# Finite representatives for normalizers of split-component centralizers

This is an internal structural construction used for the finite-normalizer
input to Renard VI.8.5.

`representativeNormalizerPoints j` is the subgroup of rational points `w` of
`G` for which conjugation restricts to an actual automorphism of the specified
group-scheme representative `j : M ⟶ G`. It records the equation
`φ.hom ≫ j = j ≫ (G.innerIso w).hom`. Composition and inversion of
automorphisms prove the subgroup laws.

The finiteness theorem assumes a field, an affine group scheme `G` of finite
type, an affine group scheme `M`, a closed embedding `j`, and a split component
`a : A ⟶ M`. Its substantive structural premise is the all-test equality
`torusCentralizer (a ≫ j) = SubgroupFunctor.range j`.
It constructs a natural number `n` and points `g : Fin n → G(k)` such that:

- Every `g t` normalizes `j` through an actual automorphism of `M`.
- Every rational point `w` normalizing `j` through an automorphism is
  `g t * rationalPoints.map j m` for some `t` and rational point `m` of `M`.

The proof restricts each normalizing automorphism to the actual split component
using `automorphismRestrictionIso`. The published finite full Weyl-image
theorem makes the range of the resulting character-lattice action finite.
Choose a representative for each value in that range and enumerate the finite
range with `Fin n`. Equal character actions imply that the quotient of a
representative and the original point centralizes the split torus, by the
published split-torus character-action kernel theorem. The supplied all-test
centralizer equality then gives an actual rational point of `M` realizing that
quotient. Multiplication gives the asserted right-coset formula.

No topology, local-field property or reductivity is used in this generic
construction. The theorem retains the centralizer premise; it does not assert
an unconditional realization of arbitrary rational Levis or prove generic
irreducibility.
