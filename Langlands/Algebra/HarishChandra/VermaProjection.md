# The Verma right ideal of a sorted weight basis and its projection

Module `Langlands.Algebra.HarishChandra.VermaProjection`, namespace
`Langlands.Algebra.HarishChandra`.

## Setting

As in `Langlands.Algebra.HarishChandra.RealWeightDecomposition`: a basis `b` of simultaneous
eigenvectors with weights `w`, an element `X ∈ H`, and real weights `realWeight w X` that
decrease along the basis order (`hd`). The basis vectors of real weight zero are assumed to lie
in `H` and to have weight `0` (`hzero`).

## The ideal

For scalars `c : Fin n → ℂ`, `basisVermaIdeal b w X c` is the sum of the positive right ideal
`realPositiveGeneratorSpan` and the span of the products `(ι(b a) - c a) v` with `b a` of real
weight zero. It is a right ideal (`basisVermaIdeal_mul_mem`). When `c` comes from a linear form
`λ` on `H`, it is the annihilator of the highest weight vector of the mirror Verma module, the
right module `U(L)/R`. Left multiplication by a generator of real weight zero preserves it
(`zero_generator_mul_mem_of_mem`), because such generators commute with each other
(`zero_letters_commute`) and act diagonally on the positive generators.

## The projection

`vermaProjection b w X c` is the linear map defined on the ordered monomial basis by
`vermaProjectionValue`:

- a monomial with a letter of positive real weight goes to `0`;
- otherwise the letters of real weight zero are replaced by the scalars `c a`, and the monomial
  of the letters of negative real weight is kept.

Main facts:

- `vermaProjection_eq_zero_of_mem_basisVermaIdeal`: the projection vanishes on the ideal. On
  the positive part this is `vermaProjection_eq_zero_of_mem` with `realPositiveGeneratorSpan_le`.
  For `(ι(b a) - c a) · monomial` there are two cases (`vermaProjection_zero_mul_monomial`). If
  the monomial has a positive letter, so does the product. Otherwise `ι(b a)` can be inserted
  into the monomial (`mul_ofFn_prod_pow_single`), and the scalar `c a` comes out.
- `sub_vermaProjection_mem`: every `u` is congruent to its projection modulo the ideal. A
  monomial without positive letters is the product of its zero-weight part and its
  negative part. On the zero-weight part each letter acts as the scalar `c a` modulo the ideal
  (`pow_mul_sub_smul_mem`, `ofFn_prod_mul_sub_smul_mem`).
- `vermaProjection_of_mem_realNegativeLetterSpan`: the projection is the identity on the span
  `realNegativeLetterSpan` of the monomials in the letters of negative real weight. Hence a
  nonzero element of that span is not in the ideal (`not_mem_basisVermaIdeal`).
