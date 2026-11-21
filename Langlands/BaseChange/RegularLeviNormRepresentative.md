# Exact norm representatives in a regular block Levi

`regularLeviNormRepresentative` proves `RegularLeviNormRepresentativeStatement`.
Let `E/F` be an extension of fields, `σ` an `F`-algebra automorphism of `E`
with `σ^l = 1`, and `B` a block shape of `n`. Suppose `δ ∈ GL_n(E)` is
norm-associated to the block diagonal element `γ = B.leviEmbedding F m`
for `m : B.Levi F`, and `γ` is regular semisimple. Then an actual twisted
conjugate `x⁻¹ δ σ(x)` is the block diagonal inclusion of `d : B.Levi E`,
with

```text
cyclicNorm σ l (d i) = baseChange F E (B.size i) (m i)
```

for every block `i`. Each `m i` is regular semisimple. In particular, every
block pair is associated by the existing `IsNormAssociated` with conjugator
`1`. No condition on the local-field topology or representations is used.
For cyclic algebras, `IsCyclicAlgebra.pow_eq_one` supplies the stated power
hypothesis.

## Why this is used

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, Mém. SMF 124 (2011), II.4.5, pp. 86–88
(PDF pp. 94–96), use twisted orbital descent at Levi representatives and
compare the ordinary and twisted character formulas on a common rational
torus. In the regular norm case the block values in that comparison must
be evaluated at associated pairs. This is a derived algebraic helper for
that step: assuming the ordinary representative is already in the Levi, it
constructs a twisted representative in that Levi with exact block norms.
The source does not state this Lean helper; we use the published cyclic norm
and conjugation conventions. No choice or enumeration of Levi embeddings,
orbital descent, or character formula is proved here.

## Implemented proof

1. **Characteristic polynomial and the centralizer.** In
   `charpoly_leviEmbedding`, reindex to the dependent block coordinates
   `B.Index`. `Matrix.BlockTriangular.charpoly` factors the characteristic
   polynomial over the nonempty index fibres. Reindexing each square block
   gives its original characteristic polynomial. This works over a
   commutative ring. Write `p_i` for the characteristic polynomial of the
   `i`-th block and `q_i = ∏_{j ≠ i} p_j`. If the whole characteristic
   polynomial is separable, `p_i` and `q_i` are coprime. Choose `c,d` with
   `c p_i + d q_i = 1`. Evaluating `d q_i` at the full block diagonal matrix
   gives the projector onto block `i`: evaluation is blockwise by the block
   diagonal algebra homomorphism, and Cayley–Hamilton gives zero on all
   other blocks and the identity on block `i`. Any commuting matrix commutes
   with the evaluation of each polynomial, by induction on the polynomial.
   Comparing the `(i,j)` entries of commutation with the projector makes
   the off-diagonal blocks vanish. `mem_leviSubgroup_of_commute_regular`
   then uses the published Levi projection of the resulting upper block
   triangular element to exhibit it in the actual Levi subgroup.
2. **Exact norm.** `IsNormAssociated.exists_cyclicNorm_eq_and_commute` uses
   the conjugator witnessing norm association as the twisted conjugator
   too. `cyclicNorm_twistedConj` and `σ^l = 1` give the exact norm. The identity
   `entrywiseAut_cyclicNorm` and the fact that base changes are fixed by σ
   give commutation of the new representative with this norm.
3. **Block norms.** `isRegularSemisimple_baseChange` gives regularity after
   base change by mapping the separable characteristic polynomial. The
   twisted representative from step 2 therefore belongs to the Levi by
   step 1. The lemmas `baseChange_leviEmbedding` (entrywise) and
   `cyclicNorm_leviEmbedding` (induction on `l`) commute the corresponding
   operations with the block embedding. Its injectivity gives equality of
   the two families of blocks and hence the displayed equalities. Each
   block characteristic polynomial divides the separable product, so each
   ordinary block is regular semisimple.

The module also proves `sigmaCentralizer_le_leviSubgroup_of_regularNorm`:
when an element has exact norm equal to a base-changed regular semisimple
Levi element, its twisted centralizer is contained in that Levi over `E`.
A twisted stabilizer of the element ordinarily centralizes its norm by
`cyclicNorm_twistedConj` and `σ^l = 1`, and step 1 applies after base change.
This only verifies the containment hypothesis of the orbital descent formula,
not the formula itself or the identification of quotient measures.
