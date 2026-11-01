# The adjacent-rank two-block analytic base

Worker 486. This module implements both exact adjacent-rank gamma and L
theorems, with the original complete upper-family conclusions.

`Langlands.RankinSelberg.twoBlockGammaAdjacentRank` has exactly the published
type `TwoBlockGammaAdjacentRankStatement.{uF,uV,uW}`. It applies
`twoBlockGammaAdjacentRank_of_transport` to the published proof
`unramifiedTwistGamma`, discharging the remaining transport premise.

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
Theorem (3.1), printed pages 404–405, gives gamma multiplicativity and the
L-factor inclusion.
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

## Gamma continuation and the closed target

The published `unramifiedTwistGamma` proves the complete symmetric spectral
transport statement in both twist positions, at all positive ranks and
independent universes. Its actual forward integral shifts by `+u`, and its
translated-dual integral shifts by `-u`. Rational rescaling and the spectral
reflection preserve the gamma equation, the model minus-one scalar,
nonzero rational witnesses, every equal-rank Fourier datum and every
unequal-rank rectangle. Its certificate assembly keeps all compatible-measure
and nonzero-functional existence witnesses and universal clauses.

The conditional consumer uses this transport to choose fixed block gamma
certificates on a sufficiently large real second-twist ray. The shared
fixed L certificates give nonzero clearing polynomials. The actual original
and translated-dual entire coefficient families, together with the
published retained-kernel Laurent bridge and spectral continuation,
specialize the real-ray gamma equation to zero. The clearing kernel is
retained until cancellation in the rational-function field; no cancellation
of a bilateral sequence is assumed.

`adjacentRankLowerCharacterGamma_of_transport` obtains an ambient complete
gamma certificate from the derived full induced Whittaker type. It extracts
an actual nonzero rational integral witness. Uniqueness of the original and
dual rational continuations then compares the specialized product equation
with the ambient equation. Scalar gamma uniqueness identifies their factors,
and this equality rewrites the entire ambient certificate. The actual
zero-deformation representation equivalence transports that certificate to
the original ordered lower induction for every quasicharacter.

`twoBlockGammaAdjacentRank_of_transport` supplies this arbitrary-character
lower theorem to `adjacentRankUpperGamma_of_lowerCharacter`. The actual
ordered-family reversal described below yields the unchanged upper-family
gamma conclusion. Applying the published `unramifiedTwistGamma` closes this
implication; no transport or analytic premise remains in the final theorem.

## Actual ordered-family reversal and the exact conclusions

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

For gamma, `IsPadicSymmetricGammaFactor.congr_equiv` transports each complete
block certificate and the induced product certificate through the same actual
ordered-family equivalences. The resulting gamma conclusion is exactly

```
∃ gamma : Fin 2 → RationalFunctions,
  (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (gamma i)) ∧
  IsPadicSymmetricGammaFactor F ψ ν.val π
    (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, gamma i).
```

Its complete measure and functional clauses, including nonzero witnesses,
are retained. The L conclusion is exactly

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
The gamma proof imports its independently published prerequisites by Lean
name. Both final theorems preserve the original full Whittaker-type inputs
and use no unrestricted multiplicativity or later rank descent.
