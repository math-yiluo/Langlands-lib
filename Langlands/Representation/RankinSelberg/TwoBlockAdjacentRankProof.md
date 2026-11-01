# The adjacent-rank two-block analytic base

Worker 486. This module implements the exact adjacent-rank L theorem.
The gamma theorem remains a separate obligation; this contribution is the
L proof record only.

`Langlands.RankinSelberg.twoBlockLAdjacentRank` has exactly the published type
`TwoBlockLAdjacentRankStatement.{uF,uV,uW}`. Its proof applies the complete
ordered-family reversal in `adjacentRankUpperL_of_lowerCharacter`, discharging
the lower analytic premise with `adjacentRankLowerCharacterL`.

The theorem retains every prime and canonical p-adic field, nontrivial
unitary additive character, supplied self-dual Haar measure, arbitrary
dependent two-block family, and independent universes `uF`, `uV`, and `uW`.
Its only arithmetic restrictions are the published `t = r + 1` and
`m 0 = 0`. The test rank is `r+1`, the induced rank is `r+2`, and the
first upper block has rank one. All representation inputs have full
Whittaker type; reducible representations are included.

## Original source and the implemented route

The source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
(1983), 367–464, registered as `jpss-1983-rankin-selberg`.
The retained original PDF has SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem (3.1), printed pages 404–405, gives the L-factor inclusion.
Section 6, printed pages 427–438, treats the lower ranks `(r+1,1)`;
§7.1, printed pages 438–439, lists this adjacent case among the three
two-block bases. These required passages were read during this task.
The task's source checks found no applicable registered JPSS erratum.

The implementation follows the source's large second twist and
continuation route through the named helper chain. The large-twist model
image and actual matrix coefficient bounds yield complete L certificates
and divisibility above a strict real bound. Unramified complete-certificate
transport fixes the two block polynomials, with the second polynomial
evaluated at the shifted spectral variable.

The arbitrary-character lower theorem then clears the actual convergent
corank spectral series on that ray. Its actual second-block Whittaker
deformation has entire coefficient dependence at a common level.
The coefficient identity theorem specializes this finite Laurent clearing
to parameter zero. The complete induced L certificate turns the resulting
model denominator bound into polynomial divisibility. The proof
constructs full induced Whittaker type and factor existence from the
original blocks, rather than assuming them.

Two formerly conditional analytic inputs are discharged by published
proofs: `twoBlockSecondWhittakerDeformation` supplies the actual
second-block deformation, and `bilateralSpectralCoefficientUniqueness`
supplies the uniqueness used by the certified real-ray clearing bridge.
The published `corankOneEntireSlice` supplies actual slice integrability
and entire dependence. Formal bilateral polynomial cancellation is not
used.

## Actual ordered-family reversal and the exact conclusion

The upper-family consumer first derives `m 1 = r` from the rank sum,
`t = r+1`, and `m 0 = 0`. It retains the original dependent carriers and
module structures while identifying the size function with `![0,r]`.
`rankOneCharacterReduction` identifies the arbitrary first rank-one block
with a lifted scalar quasicharacter representation. The original second
block is unchanged.

`glOppositeProductReversal` compares the actual normalized lower
induction with the actual upper induction after reversing the complete
ordered family: sizes, carriers, representations, and module instances.
The size adapter and the rank-one block equivalence then recover the
original upper induction
`F.canonicalNormalizedProductInduced (succBlockShape m h) σ`.
This comparison includes the normalized inducing action and the actual
smooth section representations.

Complete `IsPadicSymmetricLPolynomial` certificates transport across these
representation equivalences. The supplied self-dual measure stays fixed;
the compatible-quotient-measure existence witnesses and all universal
measure and functional clauses of the certificates remain present.
The block polynomial family is placed in upper order `(P₁,P₀)`.
Only after constructing the representation comparison does commutativity
identify its finite product with the lower-order product.

The resulting conclusion is exactly

```
∃ P Pi,
  IsPadicSymmetricLPolynomial F ψ ν.val π
    (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
  (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
  ∃ Q e, X ^ e * (∏ i, Pi i) = Q * P.
```

For reciprocal L factors this is the source inclusion: the product of the
block polynomials divided by the induced polynomial is Laurent polynomial.
The proof does not use unrestricted two-block multiplicativity, a
finite-block multiplicativity parent, or later rank descent.

Worker 1191 is credited for the included spectral-clearing bridge, and
Workers 831 and 15 for the included actual zero-comparison construction.
The exact gamma theorem is not asserted by this L contribution.
