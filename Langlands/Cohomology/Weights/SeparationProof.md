# Proof of algebraic weight separation

Worker 233 wrote this internal derived proof of the Library proposition
`Langlands.Cohomology.Weights.WeightSeparationStatement`, which is defined in
`Langlands.Cohomology.Weights.Separation`. The closing theorem is
`Langlands.Cohomology.Weights.weightSeparationStatement`. Its type is the
unchanged target `WeightSeparationStatement.{u}`, with the same universe
parameter `u` for the number field. The target pair and its imports are not
modified.

The proof uses the published modules `Langlands.Cohomology.Weights.Polynomial`
(complex weight factors) and `Langlands.Cohomology.Weights.Algebraic`
(factors over the number field and their comparison at a complex embedding).
It uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. The file opens `Classical` for the same reason as the
prerequisite files: the weight predicate `HasComplexWeight q w` has no
computable decidability instance, and the root filters need one.

## Notation

For a nonzero complex polynomial `F` and `z : ℂ`, write `m_z(F)` for
`F.roots.count z`, the multiplicity of `z` as a root. Write `ιP` for
`P.map ι` and `n` for `a.natAbs`.

## Helper lemmas

All helpers are in the namespace `Langlands.Cohomology.Weights`.

- `eq_of_monic_of_roots_eq`: two monic complex polynomials with the same
  root multiset are equal. Each one is the product of `X - C z` over its
  roots, by `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` and
  `IsAlgClosed.card_roots_eq_natDegree`.
- `eq_of_monic_of_pow_eq_pow`: if `p` and `r` are monic complex polynomials
  and `p ^ n = r ^ n` with `n ≠ 0`, then `p = r`. By `roots_pow`,
  `n • p.roots = n • r.roots`. Comparing counts with
  `Multiset.count_nsmul` and cancelling `n` gives equal root multisets.
- `count_roots_prod_of_monic`: for a finite product of monic complex
  polynomials, root multiplicities add up. This follows from `roots_prod`
  and `Multiset.count_bind`.
- `alternatingPolynomial_eq_div`: over any field `K`, the alternating
  product is the image in `RatFunc K` of the product of the even-degree `H i`,
  divided by the image of the product of the odd-degree `H i`. The proof
  splits the index set with `Finset.prod_filter_mul_prod_filter_not` and
  rewrites the exponents `(-1) ^ i` to `1` or `-1` with
  `Even.neg_one_pow` and `Odd.neg_one_pow`.
- `alternatingPolynomial_signed_count_roots`: let `R` and every `H i` be monic
  complex polynomials, and assume `alternatingPolynomial d H` equals the
  image of `R` raised to the integer power `a`. Then for every `z : ℂ`,
  `∑ i, (-1) ^ i * m_z(H i) = a * m_z(R)` in `ℤ`. Write `E` and `O` for the
  even and odd products. Then the left side equals `m_z(E) - m_z(O)` by
  `count_roots_prod_of_monic`. `Int.natAbs_eq` gives two cases. If
  `a = n`, then cancelling the nonzero image of `O` and using the
  injectivity of `algebraMap ℂ[X] (RatFunc ℂ)` gives the polynomial identity
  `E = R ^ n * O`. If `a = -n`, the same argument gives `E * R ^ n = O`. In
  both cases `roots_mul`, `roots_pow`, `Multiset.count_add` and
  `Multiset.count_nsmul` give the signed identity. This lemma covers negative
  exponents and every root multiplicity.
- `fin_eq_of_hasComplexWeight`: if one complex value has weights `i + w` and
  `j + w` for degrees `i, j : Fin (2 * d + 1)`, and `1 < q`, then `i = j`.
  This follows from `HasComplexWeight.unique` and `Fin.ext`.

## Closing theorem

After the binders are introduced, the hypotheses give that every `H i` is
monic and that every root of `H i` has complex weight `i + w`
(`IsWeilNumber.hasComplexWeight`). Since `P` is monic, `ιP` is monic, and
`alternatingPolynomial_signed_count_roots` applies with `R = ιP`.

Three consequences of the signed identity are used repeatedly.

1. If `z` is a root of `H j`, then `(-1) ^ j * m_z(H j) = a * m_z(ιP)`
   (`hat`). By `fin_eq_of_hasComplexWeight`, `z` is not a root of any other
   `H i`. So `Finset.sum_eq_single` leaves only the term for `j`.
2. If `z` is a root of no `H j`, then `a * m_z(ιP) = 0` (`haway`).
3. If `a ≠ 0`, every root of `ιP` is a root of some `H j` (`hcover`): such a
   root has positive multiplicity, so this follows from 2.

### The equivalence `a ≠ 0 ↔ ∃ i, 0 < (H i).natDegree`

- Forward: `ιP` has the same positive degree as `P` (`natDegree_map`), so
  `Complex.exists_root` gives a root `z` of `ιP`. By 3, `z` is a root of some
  `H j`. Therefore `(H j).natDegree`, which equals the number of roots of
  `H j`, is positive.
- Backward: suppose `H i` has positive degree and `a = 0`. Then
  `Complex.exists_root` gives a root `z` of `H i`, and 1 gives
  `(-1) ^ i * m_z(H i) = 0`. Both factors are nonzero, which is a
  contradiction. This is the `a = 0` case.

### Existence of the separation when `a ≠ 0`

Then `n ≠ 0`. For a root `z` of `H j`, the lemma `hmult` derives two facts
from 1:

- `m_z(H j) = n * m_z(ιP)` in `ℕ`, by taking `Int.natAbs` of both sides.
- `0 < (-1) ^ j * a`. Multiplying by `(-1) ^ j` gives
  `m_z(H j) = ((-1) ^ j * a) * m_z(ιP)`, and `m_z(H j)` is positive.

By 3, every root of `ιP` is a root of some `H j`. So every root of `ιP` is a
Weil number of some weight, including the condition at its rational
conjugates. This root hypothesis of `map_algebraicWeightFactor` is therefore
proved from the signed identity, not assumed.

The factors are `Q j := algebraicWeightFactor q (j + w) P` over `L`. The
published construction keeps exactly the normalized irreducible factors of
`P` that are pure of weight `j + w`.

- Purity of weight `j + w`, including monicity: `algebraicWeightFactor_isPure`.
- Coefficient descent: `map_algebraicWeightFactor` with the embedding `ι`
  used twice gives
  `(Q j).map ι = complexWeightFactor q (j + w) ιP`. The root multiset of the
  right side is the set of roots of `ιP` of weight `j + w`, with their
  multiplicities (`roots_complexWeightFactor`).
- `H j = (Q j).map ι ^ n`: both sides are monic, so by
  `eq_of_monic_of_roots_eq` it suffices to compare multiplicities at each `z`.
  The right side has multiplicity `n * m_z(ιP)` if `z` has weight `j + w`,
  and `0` otherwise. If `z` is a root of `H j`, it has weight `j + w`, and
  `hmult` gives `m_z(H j) = n * m_z(ιP)`. If `z` is not a root of `H j` but
  has weight `j + w`, then `z` is not a root of `ιP`. Otherwise, by 3, it
  would be a root of some `H k` of weight `k + w`, which forces `k = j`. If
  `z` does not have weight `j + w`, both sides are `0`.
- `Q j = 1` when `(-1) ^ j * a < 0`: no root of `ιP` has weight `j + w`.
  Such a root would be a root of some `H k` with `k = j`, and `hmult` would
  give `0 < (-1) ^ j * a`. So `complexWeightFactor_eq_one` gives
  `(Q j).map ι = 1`. Then `Polynomial.map_injective`, using the injectivity
  of the field homomorphism `ι`, gives `Q j = 1`.
- `∏ j, Q j = P`: by injectivity of `Polynomial.map ι` and
  `Polynomial.map_prod`, it suffices to show that the product of the complex
  weight factors of `ιP` over all degrees is `ιP`. Both sides are monic, so
  multiplicities are compared with `count_roots_prod_of_monic`. If `z` is a
  root of `ιP`, then by 3 it is a root of some `H k`. Only the degree `k` has
  matching weight (`fin_eq_of_hasComplexWeight`), so the sum is
  `m_z(ιP)`. If `z` is not a root of `ιP`, every term is `0`.

### Uniqueness

Let `Q'` be any family satisfying `IsWeightSeparation`. For each `j`, its
purity clause makes `Q' j` monic, and `(Q' j).map ι ^ n = H j = (Q j).map ι ^ n`.
`eq_of_monic_of_pow_eq_pow` (with `n ≠ 0`) and the injectivity of
`Polynomial.map ι` give `Q' j = Q j`. Uniqueness uses only the purity and
power clauses of `Q'`.

## Scope and provenance

This is an internal derived proof of the published algebraic target. The
target's paired Markdown records the motivating source: Kottwitz (1992),
Section 6, literature ID `kottwitz-1992-lambda-adic-simple-shimura`. The
implemented route uses root multiplicities in `ℂ[X]` and the Library's
weight-factor constructions. It is not presented as a transcription of the
source's argument.

The theorem proves only the algebraic implication stated by the target. It
constructs no cohomology or Galois representation and supplies no trace
identity, purity theorem or removal of representation multiplicities. These
remain hypotheses or outside the statement.
