# Normalized covariant coordinates from top weight lines

Worker 1161. This module is internal and derived. It turns the published
extremal-line construction of `Reductive.ExtremalMatrixCoefficient` into normalized
covariant coordinates for the parabolic subgroups attached to an arbitrary
cocharacter. It also proves the pairing, conjugation and centralizer lemmas used to
control the resulting characters. All statements hold on every relative test
scheme over `Spec k`, for any field `k`. The construction is the classical one
(Milne, *Algebraic Groups* (2017), Chapter 22; Chevalley's line argument). Take
the top exterior power of the top weight space of a cocharacter, and use its
coordinate line in an exterior power of a representation. No literature statement
is formalized verbatim.

## Restriction and normalization helpers

- `characterEval_characterRestrict`: evaluating a restricted character is
  evaluating the original character at the image point.
- `mem_leftCovariantSubspace_restrict`: let `f` be left covariant along
  `iP : P → G` for the coordinate of a character `ψ` of `P`. If `fP ≫ iP = i`, then
  `f` is left covariant along `i` for the coordinate of `ψ ∘ fP`. The proof uses
  the all-test criterion `mem_leftCovariantSubspace_iff_points`.
- `counit_eq_one_of_forall`: a coordinate with value one at the identity point of
  every test has counit one.

## The top weight coefficient

`exists_topWeight_coefficient` takes the following data.

- An actual matrix representation `ρ : G → GL_N` and a cocharacter `χ` of `G`
  with `χ ≫ ρ` equal to the diagonal cocharacter of weights `e`.
- An upper bound `M` for the weights.
- Representatives `iP` of the dynamic parabolic of the opposite cocharacter
  and `iQ` of the dynamic parabolic of `χ`.
- A group `H` with `i = fP ≫ iP`.
- A group `U` with `j = κ ≫ iQ`, such that every character of `Q` is trivial on
  the points of `U` through `κ`.

It produces a character `ψ` of `P` and a coordinate `f` of `G` with the following
properties:

- `f` is left covariant along `i` for the coordinate of `ψ ∘ fP`;
- `f` is right invariant along `j`;
- `f` has counit one;
- `ψ` takes the value `t ^ (topCard e M * M)` at every point of `P` whose image
  in `G` is `χ(t)`.

Proof. Let `d = topCard e M` and `ρ'` be the `d`-th exterior power of `ρ`. By
`diagonalCocharacter_comp_exteriorGroupHom`, `χ ≫ ρ'` is diagonal with the weights
`w(s) = Σ_{a∈s} e a`. Hence the opposite cocharacter `ν` has weights `-w`
(`oppositeCocharacter_comp`). By `sum_lt_sum_topPoint`, the top subset `s₀` is the
unique coordinate of smallest `ν`-weight. The published
`diagonalMatrixCoefficient_mem_leftCovariantSubspace` makes the diagonal
coefficient of `ρ'` at `s₀` left covariant for the minimum-weight character `ψ` on
`P = P(ν)`. Restriction along `fP` gives the first property.
`pointAlgebraHom_mul_inv_diagonalMatrixCoefficient` gives inverse-right covariance
along `P(ν⁻¹) = P(χ)`. Its character factor is trivial on points of `U`, by the
hypothesis on `U`, which gives right invariance. The coefficient is one at the
identity. Finally, `minimumWeightCharacter_eval` evaluates `ψ` as the `(s₀, s₀)`
entry of `ρ'`. At `χ(t)` this entry is `t ^ w(s₀)`, and `w(s₀) = topCard e M * M`
by `sum_topPoint`.

## Pairings, conjugation and centralizers

- `latticePairing_eq_of_points`: if a character `σ` of a commutative group scheme
  `T` takes the value `t ^ c` at `μ(t)` for every point `t` of `𝔾_m`, then
  `⟨σ, μ⟩ = c`. The composite `μ ≫ σ` agrees on points with the `c`-th power map,
  which is `(gmEndEquiv k).symm c`.
- `innerIso_hom_comp_character`: rational characters are invariant under inner
  automorphisms, because the multiplicative group is commutative.
- `mem_centralizer_of_comp_innerIso`: a rational point `n` with
  `χ ≫ inn(n) = χ` lies in the dynamic centralizer of `χ`. The proof uses the
  published identification `torusCentralizer_gm_eq_dynamicCentralizer` and the
  point formula for inner automorphisms.
- `characterAut_characterRestrict_eq`: let `n` be a rational point of `G`
  normalizing `incl : T → G` through `σ`, and suppose `n` comes from a rational
  point `n'` of `P`, where `iP : P → G` is a monomorphism and `tP ≫ iP = incl`.
  Then for every character `ψ` of `P`, the torus character `ψ ∘ tP` is fixed by
  `characterAut σ`. Conjugation by `n'` restricts along `tP` to `σ`, by cancelling
  the monomorphism `iP` (with `innerIso_hom_comp`). Characters are invariant under
  conjugation.
