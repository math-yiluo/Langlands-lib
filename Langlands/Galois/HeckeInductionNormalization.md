# Unitary normalization of induced Euler polynomials of `χ · ‖·‖^{b/2}`

Let `E/K` be an extension of number fields, `χ` a unitary Hecke character of
`E` and `b` a natural number. The main theorem
`matchesHeckeInduction_normPower` states that if complex polynomials `Q v`
agree almost everywhere with the induced unramified Euler polynomials of
`χ · ‖·‖^{b/2}` (`MatchesHeckeInductionEulerPolynomials`), then:

- their unitary normalizations `unitaryEulerPolynomial (Q v)` agree almost
  everywhere with the induced Euler polynomials of `χ`, and
- for almost all `v`, `Q v` has constant coefficient `1` and the reversed
  polynomial `(Q v).reverse` has complex roots of weight `-b` for the residue
  cardinality `q_v` (`HasComplexRootsOfWeight`), that is, of absolute value
  `q_v^(-b/2)`.

## Proof

At a place `w` of `E` above `v` with residue degree `f`, a uniformizer has
norm `q_w⁻¹ = q_v^(-f)` (`norm_uniformizer`, Mathlib's
`Ideal.absNorm_pow_inertiaDeg`). Hence `‖·‖^{b/2}` takes the value
`r^f` at it, with `r = radius q_v (-b) = q_v^(-b/2)`
(`normPower_uniformizer`). This is the factor `q_v^(-b f/2)` of the Markdown
of `Langlands.Global.Arithmetic.HarrisProposition48SingletonMonomialStatement`.
The induced polynomial of `χ · ‖·‖^{b/2}` is therefore
`∏_w (1 - χ_w(ϖ_w) r^{f_w} X^{f_w})`, with `|χ_w(ϖ_w)| = 1`.

The polynomial lemmas compute the normalization of such a product
(`unitaryEulerPolynomial_prod_scaled`). Its reverse is
`∏ (X^{f_i} - c_i r^{f_i})` (`reverse_prod_one_sub`). This polynomial is
monic, and all its roots have absolute value `r` (`norm_eq_of_mem_roots_prod`).
Hence it has weight `-b`. The Library theorem
`unitaryEulerFromEigenvalues_eq_weight_substitution` computes the
normalization of a monic polynomial of known weight by the substitution
`X ↦ X / r`. Reversing back (`reverse_reverse_of_coeff_zero_ne`) gives
`∏ (1 - c_i X^{f_i})`, the induced polynomial of `χ`. Unramifiedness of `χ`
above `v` follows from that of `χ · ‖·‖^{b/2}`, because `‖·‖^{b/2}` is
unramified everywhere (`HeckeCharacter.normPower_isUnramifiedAt`).

`reverse_map_of_injective` records that reversal commutes with an injective
coefficient map. It is used to move the weight statement between `L[X]` and
`ℂ[X]`.

## Source

The normalization is Harris's convention of dividing each eigenvalue by its
absolute value. The half-integral twist `‖·‖^{b/2}` and the resulting weight
follow the remark of Harris 1998 (`harris-1998-local-langlands`), p. 191,
companion TeX lines 866–875, and Lemma 1.6, pp. 188–189, lines 704–744.
