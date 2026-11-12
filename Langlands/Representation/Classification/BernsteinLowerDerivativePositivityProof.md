# Proof of lower shifted-derivative positivity for irreducible unitary representations

Module `Langlands.Representation.Classification.BernsteinLowerDerivativePositivityProof`,
namespace `Langlands.Classification`.

## Target

`bernsteinUnitaryLowerDerivativePositivity F T :
BernsteinUnitaryLowerDerivativePositivity.{uF, uV} F T`. This is the Library statement
in `Langlands/Representation/Classification/BernsteinLowerDerivativePositivityStatement.lean`.
Let `π` be an irreducible unitarizable smooth representation of `GL_N(F)`, `N > 0`, with
highest derivative order `h` (`hd : GeneralLinearHighestDerivativeOrderData T ψ π`).
Then every irreducible subquotient of `ν^(1/2) π^(k)`, `k < h`, has a strictly
positive Bernstein central exponent.

## Source

J. N. Bernstein, *P-invariant distributions on GL(N) and the classification of unitary
representations of GL(N) (non-archimedean case)*, LNM 1041 (1984)
(`bernstein-1984-p-invariant`), §7.4, printed p. 83 (PDF p. 34). The positive orders
follow Bernstein's argument, without his sheaf language. The order-zero case is the
elementary extension described in the statement's Markdown (§8.2).

## Theorems in this module

- `isUnitarizable_phiMinusIterate F T hU ψ n j B`: given
  `hU : Derivative.MirabolicPhiMinusUnitarity.{uF, uV} F T`, the iterate
  `(Φ⁻)^j B = (phiMinusIterate T ψ n j).obj B` of a unitarizable `B` on
  `mirabolic (n + j) F` (carrier universe `max uF uV`) is unitarizable. The proof is
  by induction on `j`. `phiMinusIterate T ψ n (j + 1)` is definitionally
  `phiMinus T ψ (n + j) ⋙ phiMinusIterate T ψ n j`, and `hU` handles one step.
- `isUnitarizable_generalLinearRestriction F T π`: the mirabolic restriction
  `(generalLinearRestriction T N).obj π` of a unitarizable `π` on `GL_(N+1)` is
  unitarizable. The restriction has the same carrier and acts by `π ∘ subtype`, so the
  same form is invariant.
- `bernsteinPositiveCentralExponents_succ F T hU ψ ha hn π hirr hunit hh hkh hnz hadm`
  covers the positive orders. Let `π` be irreducible and unitarizable on `GL_a`, with
  `ha : a = n + k' + 1` and `0 < n`. Assume `π` has a nonzero derivative of some order
  `h` with `k' + 1 < h`, and that the shifted derivative
  `ν^(1/2) (generalLinearDerivativePositive T ψ n k').obj ((generalLinearRankCast T ha).obj π)`
  is admissible. Then that shifted derivative has positive central exponents. The rank
  `a` is a variable so that `subst ha` turns the rank cast into the identity.
- `bernsteinUnitaryLowerDerivativePositivity_of_phiMinusUnitarity F T hU`: the target
  statement, assuming `hU`.
- `bernsteinUnitaryLowerDerivativePositivity F T`: the target statement, obtained by
  supplying the Library theorem
  `Derivative.Mirabolic.mirabolicPhiMinusUnitarity.{uF, uV} F T` as `hU`.

## Proof of the positive-order step

After `subst ha`, write `n = m + 1`. Let `R = (generalLinearRestriction T (m + 1 + k')).obj π`
(on `mirabolic (m + 1 + k')`) and `τ = (phiMinusIterate T ψ (m + 1) k').obj R` (on
`mirabolic (m + 1)`). The shifted derivative is definitionally
`T.segmentFactor ((psiMinus T (m + 1)).obj τ) (1 / 2)`.

1. Level of `R`. By `Aubert.ZelevinskyHighestDerivative.hasNonzeroDerivative_restriction_iff`,
   the nonzero order-`h` derivative of `π` gives `HasNonzeroDerivative T ψ R h`. Then
   `le_level_of_hasNonzeroDerivative` gives `h ≤ level T ψ R`, so
   `k' + 2 ≤ level T ψ R`.
2. Homogeneity. `Mirabolic.isHomogeneous_restriction_of_isIrreducible` (module
   `MirabolicHomogeneousDescent`) makes `R` homogeneous.
   `Mirabolic.isHomogeneous_phiMinusIterate` then makes `τ` homogeneous with
   `level τ + k' = level R`, so `level τ ≥ 2`. `Mirabolic.eq_zero_of_radical_fixed`
   shows that every vector of `τ` fixed by the whole radical `radical (m + 1) F` is zero.
3. Unitarity. `R` is unitarizable by `isUnitarizable_generalLinearRestriction`, so `τ`
   is unitarizable by `isUnitarizable_phiMinusIterate`.
4. Contraction. `Mirabolic.norm_lt_one_of_radical_eigen T m` (module
   `MirabolicRadicalContraction`) applies to `τ` by steps 2 and 3. Let `y` have a nonzero
   class in the radical coinvariants, and suppose that class is a `c`-eigenvector of
   `levi (scalar ϖ)`. Then `‖c‖ < 1`.
5. Reduction. `bernsteinPositiveCentralExponents_segmentFactor_psiMinus` (module
   `BernsteinDerivativeEigenvector`) turns step 4, together with the admissibility
   hypothesis, into positivity of every central exponent of
   `T.segmentFactor ((psiMinus T (m + 1)).obj τ) (1 / 2)`.

## Proof of the target

Introduce `N`, `0 < N`, `ψ`, `π`, irreducibility, unitarizability, `hd`, and an order
`k ≤ N` with `k < hd.order`.

- `k = 0`: `bernsteinShiftedDerivative_zero_positive` (module
  `BernsteinOrderZeroPositivity`).
- `k = k' + 1`: `bernsteinShiftedDerivative T ψ π (k' + 1) hk` is definitionally
  `T.segmentFactor ((generalLinearDerivativePositive T ψ (N - (k' + 1)) k').obj
  ((generalLinearRankCast T (rank_eq_of_succ_le hk)).obj π)) (1 / 2)`. Apply
  `bernsteinPositiveCentralExponents_succ` with `a = N`, `n = N - (k' + 1)`. This `n`
  is positive because `k' + 1 < hd.order ≤ N`. Take `h = hd.order` with
  `hnz = hd.nonzero`, and admissibility from `bernsteinShiftedDerivative_isAdmissible`.

## Helper modules shipped with this proof

- `Langlands/Representation/Derivative/MirabolicRadicalContraction` (radical averaging).
- `Langlands/Representation/Derivative/MirabolicHomogeneousDescent` (homogeneity
  through `Φ⁻`).
- `Langlands/Representation/Classification/BernsteinOrderZeroPositivity` (order zero).
- `Langlands/Representation/Classification/BernsteinDerivativeEigenvector`
  (eigenvectors of the uniformizer on admissible shifted derivatives).

Each has its own paired Markdown.
