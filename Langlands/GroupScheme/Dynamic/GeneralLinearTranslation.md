# Right translation on the polynomial ring of the coordinates of `GL_n`

This internal unit builds the finite-dimensional representations of `GL_n` that the stabilizer
argument for the opposite cell needs. They are right translation on polynomials of bounded
degree in the matrix coordinates. The unit then shows how block parabolic, block unipotent and
diagonal matrices act in the basis of monomials.

Throughout, `n` is a finite index type and `S` an arbitrary commutative ring. The coordinates
`Coordinate n` of `GL_n` from `GeneralLinear` are the matrix entries `x_{ij}` (`.entry i j`) and
the entries `y_{ij}` of the inverse matrix (`.inverseEntry i j`). `coordinateEquiv`
identifies them with `(n × n) ⊕ (n × n)`. This equivalence provides the `Fintype` and
`DecidableEq` instances.

## Right translation

For `g : GL n S`, `translate g` is the `S`-algebra endomorphism of `S[x_{ij}, y_{ij}]` sending
`x_{ij}` to `∑ₗ x_{il} g_{lj}` and `y_{ij}` to `∑ₗ (g⁻¹)_{il} y_{lj}` (`translationImage`).

* `aeval_values_translate`: for an `S`-algebra `R` and `x : GL n R`, evaluating
  `translate g F` at the coordinates of `x` is evaluating `F` at the coordinates of `x g`. The
  proof compares both sides on the variables. For `y_{ij}` it uses `(x g)⁻¹ = g⁻¹ x⁻¹`.
* `translate_one` and `translate_mul`: `translate 1` is the identity, and
  `translate (g h) = translate g ∘ translate h`. Both are checked on the variables.
* `isHomogeneous_translate` and `totalDegree_translate_monomial_le`: each variable goes to a
  homogeneous polynomial of degree `1`. So translation preserves homogeneous polynomials of each
  degree, and the translate of `X^m` has total degree at most `deg m`.

## The representation on polynomials of degree at most `d`

`Exponent n d` is the finite type of exponents `m` of total degree at most `d`.
`eq_sum_exponent` writes a polynomial of total degree at most `d` as the sum of its monomials
with such exponents.

`translationMatrix d g` is the matrix over `Exponent n d` whose entry `(m', m)` is the
coefficient of `X^{m'}` in `translate g (X^m)`. `coeff_translate` states that the coefficient
vector of `translate g F` is this matrix times the coefficient vector of `F` whenever
`deg F ≤ d`. From it and the two identities above follow `translationMatrix_mul` and
`translationMatrix_one`. Together they give the group homomorphism
`translationHom S d : GL n S →* GL (Exponent n d) S`.

## Weights

Fix `e : n → ℤ`. `coordinateWeight e` gives `x_{ij}` the weight `e j` and `y_{ij}` the weight
`-e i`. `monomialWeight e m` is the weighted degree of `m`, which is additive. Negating `e`
negates the weights (`coordinateWeight_neg`). The submodules `weightGE e c`, `weightLT e c`
and `weightLE e c` consist of the polynomials whose monomials all have weight `≥ c`, `< c` and
`≤ c`. The products of such polynomials obey the expected bounds (`mul_mem_weightGE`,
`mul_mem_weightLT_of_le`, `mul_mem_weightLT_of_lt`, `prod_mem_weightGE`, `pow_mem_weightGE`).

* `aeval_monomial_mem_weightGE`: suppose an algebra map sends every variable `v` to a
  polynomial of weight at least the weight of `v`. Then it sends `X^m` to a polynomial of
  weight at least `monomialWeight e m`.
* `IsUnipotentAt e m F` means that `F - X^m` has only monomials of weight less than the weight
  of `m`. This property is closed under products and powers, and `1` has it at `0`.
* `isUnipotentAt_aeval_monomial`: if an algebra map sends every variable `v` to `v` plus terms
  of smaller weight, then it sends `X^m` to `X^m` plus terms of smaller weight.

## Block matrices and the diagonal

* `translationImage_mem_weightGE`: let `g` be block parabolic for `e`, meaning `g_{ij} = 0`
  when `e i < e j`. Then the translate of each coordinate has weight at least that of the
  coordinate. For `x_{ij}`, a term `x_{il} g_{lj}` with `g_{lj} ≠ 0` has `e j ≤ e l`. For
  `y_{ij}`, the inverse `g⁻¹` is block parabolic, so a term `(g⁻¹)_{il} y_{lj}` with nonzero
  coefficient has `-e i ≤ -e l`.
* `translationHom_mem_blockParabolicSubgroup`: hence `translationHom S d g` is block parabolic
  for the monomial weights `m ↦ monomialWeight e m`. An entry `(m', m)` with
  `weight m' < weight m` is a coefficient below the weight bound, so it vanishes.
* `translationImage_isUnipotentAt`: let `g` be block unipotent for `-e`, meaning
  `g_{ij} = δ_{ij}` when `e j ≤ e i`. Then the translate of each coordinate is the coordinate
  plus terms of smaller weight. The proof subtracts the coordinate, written as its translate by
  the identity matrix, and inspects the coefficients `g_{lj} - δ_{lj}` and
  `(g⁻¹)_{il} - δ_{il}`.
* `translationHom_mem_blockUnipotentSubgroup`: hence `translationHom S d g` is block unipotent
  for the negated monomial weights. By `coeff_eq_of_isUnipotentAt`, an entry `(m', m)` with
  `weight m ≤ weight m'` is the identity entry `δ_{m'm}`.
* `translationImage_diagonalUnits` and `translate_diagonalUnits_monomial`: translation by
  `diag(t ^ e i)`, for a unit `t`, multiplies each coordinate and each monomial `X^m` by `t` to
  its weight. The monomial case is an induction on `m`.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups* (2nd edition), prove Proposition 2.1.8(3) over
a field (Step 3) with the stabilizer argument, applied to a representation of the ambient
`GL(V)` in which the subgroup is the stabilizer of a line. This development works with
the explicit representations on polynomials of bounded degree in the coordinates instead. The
constructions and weight computations here are internal.
