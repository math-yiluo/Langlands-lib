# Leading monomials of the moment symbols

Polynomials `Pol n` in the coordinates `v_p` (`vV p`) and the dual coordinates `ξ_p` (`xV p`),
`p` running over the positions strictly below the diagonal (`Lw n`).

## Definitions

- `MVar n`: the variables; `key`: a sort key making `MVar n` linearly ordered (dual coordinates
  first, ordered by row ascending and then column descending; then the coordinates, ordered by
  jump `a - c` descending and then row). `ord n` is the lexicographic monomial order for this
  order.
- `VOnly f`: `f` involves only the coordinates `v`.
- `lowMatG w`, `upPart M`: the strictly lower triangular matrix with entries `w`, and the strictly
  upper part of a matrix.
- `nbF = 1 + lowMatG v`, `nbInvF` its adjugate (= inverse, `nbF_det = 1`), `xiMat = lowMatG ξ`,
  `UF = upPart (nbF xiMatᵀ)`, `PhiF = nbInvF · UF · nbF`.
- `symb`: `2N` chosen entries of `Φ`, `Φ_{jk}` for the position `(k, j)` and `Φ_{a, c+1}` for the
  position `(a, c)` (`succCol`); `symbDeg` their leading monomials; `prodSymb α = ∏_i symb_i^{α_i}`.

## Results

- `degree_nbInvF`: for `c < a`, the leading term of `(nb⁻¹)_{ac}` is `-v_{ac}` (by the recursion
  `nbInvF_eq` coming from `nb · nb⁻¹ = 1`; the other monomials only involve smaller jumps).
- `PhiF_apply`: `Φ_{ab}` is the sum of the terms `phiTerm`, each a polynomial in `v` times one
  `ξ`; `phiTerm_support_lt`, `lt_of_xV_lt`, `degree_add_of_support_lt`: a term with a less
  significant `ξ` has smaller monomials.
- `PhiF_upper`: for `a < b`, `Φ_{ab}` has leading monomial `ξ_{ba}` with coefficient `1`.
- `PhiF_lower`: for `c < a` and `c₁ = c + 1`, `Φ_{a c₁}` has leading monomial
  `ξ_{c₁ c} v_{a c}` with coefficient `-1`.
- `degree_symb`, `degree_prodSymb`: the degree of `prodSymb α` is `Σ_i α_i · symbDeg i`;
  `degSum_injective`: this determines `α` (the `v`-part of `symbDeg (inl p)` is the single
  coordinate `v_p`, and the remaining `ξ`-parts then determine the other exponents).
- `linearIndependent_of_degree_injective`: polynomials with pairwise distinct leading monomials are
  linearly independent; hence `linearIndependent_prodSymb`: the family `α ↦ prodSymb α` is
  linearly independent.

## Provenance

Internal infrastructure for the proof of `ComplexStandardHolomorphicGrowthStatement`
(Library module `ComplexLinkedLanglandsQuotientGrowth`); see
`ComplexStandardHolomorphicGrowthProof.md` for the overall argument. The module introduces no
statement from the literature, and all its results are proved here.
