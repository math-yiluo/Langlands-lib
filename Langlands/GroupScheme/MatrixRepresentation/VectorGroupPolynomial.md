# Polynomial coefficient operators of actual vector-group representations

This is a derived construction from the actual vector-group scheme and its
matrix representations. The first part works over any commutative base ring
`R`, with vector-group dimension `d : ℕ` and a finite coordinate index type `n`.
The operator and coefficient-recovery results work over a field `k`.

`VectorGroup.affinePoint S t` is the spectrum of the polynomial evaluation
algebra map at `t : Fin d → S`. The theorem
`VectorGroup.affinePointsEquiv_affinePoint` identifies its image under the
actual corepresented point equivalence with `Multiplicative.ofAdd t`.
Consequently these points exhaust all affine points over `S`
(`affinePoint_surjective`), zero coordinates classify the identity, and vector
addition classifies multiplication (`affinePoint_zero`, `affinePoint_add`).

The remaining declarations are in
`Langlands.GroupScheme.MatrixRepresentation.VectorGroupPolynomial`.
For an actual group-scheme representation
`ρ : MatrixRepresentation (VectorGroup.groupScheme R d) n`,
`polynomialMatrix ρ` is the underlying matrix of `ρ.affineMatrix` at the
identity morphism of the vector group's spectrum. Its entries belong to
`MvPolynomial (Fin d) R`. This is a universal point over the polynomial
coordinate algebra, rather than a choice of base-field values.
`polynomialMatrix_aeval` proves

`(polynomialMatrix ρ).map (MvPolynomial.aeval t) =
  (ρ.affineMatrix S (VectorGroup.affinePoint S t) : Matrix n n S)`

for every commutative `R`-algebra `S`. The proof is precisely naturality of the
actual affine matrix along the evaluation algebra map. No reducedness,
infinitude or field assumption is needed for this comparison.

For a matrix `M : Matrix n n (MvPolynomial σ k)` over a field, with an arbitrary
variable type `σ`, `matrixCoefficients M` collects its coefficient matrices as a
finitely supported function on `σ →₀ ℕ`. Its value at multi-index `a` has entry
`(M i j).coeff a`. Its support lies in the finite union of the supports of the
entries. The construction proves that an index outside this union has every
matrix entry zero, so the resulting family really has finite support.
`evaluation_matrixCoefficients` shows that evaluating this family by
`LinearAlgebra.PolynomialCoefficients.evaluation` is entrywise scalar polynomial
evaluation. The proof applies the scalar-polynomial comparison to each entry
projection and identifies the scalar polynomial by its coefficients.

`operatorCoefficients M` maps this family through `Matrix.toLin'`, the linear
equivalence from matrices to endomorphisms of column vectors `n → k`.
`operatorCoefficients_apply` gives its coefficient formula, and
`evaluation_operatorCoefficients` proves that evaluation commutes with this
matrix-to-operator passage by the general `map_evaluation` theorem.

For an actual vector-group representation over `k`, `coefficientOperators ρ`
specializes this construction to `polynomialMatrix ρ`.
`pointOperator ρ x` is the underlying linear map of the actual
`ρ.affineAction (CommAlgCat.of k k) x`. The theorem
`evaluation_coefficientOperators` identifies evaluation of the coefficient
operators at `t : Fin d → k` with `pointOperator ρ (VectorGroup.affinePoint _ t)`.
The proof combines the matrix evaluation identities and the actual affine
action's column-vector formula. `pointOperator_one` and `pointOperator_mul`
retain the representation laws, and `pointOperator_commute` follows from
commutativity of vector addition and the point classification.

If `k` is infinite, the following three comparisons follow from the general
coefficient-recovery results, together with surjectivity of `affinePoint`:

- `invariant_affinePoints_iff_invariant_coefficients`: a `k`-submodule of
  `n → k` is stable under every actual affine base-field point action if and
  only if it is stable under every coefficient operator.
- `span_range_pointOperator_eq_span_range_coefficients`: these actual point
  operators and all coefficient operators have equal linear spans.
- `adjoin_range_pointOperator_eq_adjoin_range_coefficients`: these families
  generate equal unital `k`-subalgebras of `Module.End k (n → k)`. Its proof
  applies algebraic adjoining to the span equality.

Finally, `coefficientOperators_commute` proves that every pair of coefficient
operators commutes over an infinite field. First apply coefficient recovery
to the underlying submodule of the centralizer of all point operators: the
commuting point actions put every coefficient in that centralizer. For a fixed
coefficient, every polynomial value then belongs to its centralizer. A second
coefficient-recovery step puts every coefficient there too.

All results are derived from the explicitly represented vector group, actual
matrix/action naturality, finite polynomial coefficients and the general
coefficient-recovery argument. No external literature theorem is assumed.
Infinitude is retained for all coefficient-recovery conclusions, including
coefficient commutation. These results do not establish divided-power
composition identities or construct a highest-weight or Steinberg module.
They do not prove `Langlands.GroupScheme.SteinbergBigCellStatement`.
