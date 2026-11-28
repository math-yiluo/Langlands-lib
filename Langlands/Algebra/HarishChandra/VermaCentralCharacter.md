# Central characters of mirror Verma modules

Module `Langlands.Algebra.HarishChandra.VermaCentralCharacter`, namespace
`Langlands.Algebra.HarishChandra`.

The setting is that of `Langlands.Algebra.HarishChandra.VermaProjection`: a sorted weight basis
`b` with weights `w`, `X ∈ H`, and the right ideal `basisVermaIdeal b w X c`.

## Contents

- `eq_of_sub_mem_of_mul_sub_mem`: let `R` be a right ideal of an algebra, `z` an element
  commuting with `u₀`, and `s₁, s₂` scalars. If `z - s₁ ∈ R`, `u₀ (z - s₂) ∈ R` and
  `u₀ ∉ R`, then `s₁ = s₂`. Indeed `(s₂ - s₁) u₀ = (z - s₁) u₀ - u₀ (z - s₂)`. This compares
  central characters through a singular vector `u₀`.
- `exists_polynomial_sub_mem_basisVermaIdeal`: an element `z` commuting with `H` is congruent
  to a scalar modulo `basisVermaIdeal b w X (c₀ + t • c₁)`. The scalar is the value at `t` of a
  polynomial `P`. Write `z = p + q` by `mem_sup_of_commute_of_antitone`, with `p` in the
  positive right ideal and `q` a combination of monomials in the zero-weight letters. Then
  `q` is congruent to its projection, and on such monomials the projection is the product of
  the powers of the parameters (`vermaProjection_monomial_eq`), a polynomial in `t`
  (`vermaMonomialPolynomial`).
- `eq_zero_of_algebraMap_mem_basisVermaIdeal`: a scalar lies in the ideal only if it is `0`,
  since the projection fixes scalars and vanishes on the ideal.
- `mul_mem_of_basisVermaIdeal`: if `u₀` multiplies the generators of the ideal into a right
  ideal `R`, it multiplies the whole ideal into `R`.
- `realNegativeLetterSpan_mul_mem` and `vermaProjection_mem_realNegativeLetterSpan`: the span of
  the monomials in negative letters is closed under products when the negative basis vectors
  span a Lie subalgebra, and the projection takes values in it.
- `exists_eq_mul_of_mem_sup`: let `v₀` be in the negative span and multiply the ideal for `c'`
  into the ideal for `c`. Then an element `u` of the negative span of the form `r + v₀ x`, with
  `r` in the ideal for `c`, equals `v₀ y` for some `y` in the negative span. Take `y` to be the
  projection of `x` for `c'`. Then `u - v₀ y` lies in the ideal for `c` and in the negative
  span, so it vanishes.
