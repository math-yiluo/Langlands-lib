# Local pair data of a character twist

Supporting module of the gamma comparison for weakly associated cuspidal pairs (module
`Langlands.Automorphic.AssociatedGammaTwistedPairData`). It defines the finite local factors
of the automorphic Hecke Euler family used in the proof of `AssociatedGammaStatement`
(Henniart 2000, Théorème 2.3). At a finite place `z` and for a Hecke character `χ`, the
factor depends on `χ` only through its local component `η = χ_z`: it is built from the
Rankin–Selberg factors of the local class pair `(π_z ⊗ η, π'_z)`. Internal construction;
the only mathematical inputs are the published local existence theorems.

## Definitions

- `Correspondence.IsTwistedPairData K ψ ν π π' η d`, for `d = (P, Pd, e)`: there are classes
  `πη`, `πd`, `πd'` with `IsCharacterTwist K η π πη`, `IsSmoothDual K πη πd`,
  `IsSmoothDual K π' πd'`, `P` the pair L-polynomial of `(πη, π')`, `Pd` that of
  `(πd, πd')`, and `e` the pair epsilon factor of `(πη, π')`, all at `ψ` and `ν`. These are
  exactly the witnesses of the published `IsAutomorphicPairGammaFactor` for `(πη, π')`.
- `Correspondence.twistedPairData ψ ν π π' η`: a choice (`Classical.epsilon`) of such data.
- `FunctionalEquationComparison.pairDataFactors q d`: the local factors
  `1 / P(q^-s)`, `1 / Pd(q^-s)`, `c q^(-m s)`, in the shape of
  `FinitePairFactorChoice.localFactors`.

## Results

- `IsCharacterTwist.unique`, `IsSmoothDual.unique`: twists and smooth duals of a class are
  unique (published `isCharacterTwist_iff_eq_twist` with the open kernel
  `isOpen_ker_determinantQuasiCharacter`, and `isSmoothDual_iff_eq_contragredient`).
- `isCharacterTwist_one`: every class is its own twist by the trivial character
  (`Langlands.twist_one`).
- `exists_isTwistedPairData`, `twistedPairData_spec`: for a self-dual measure the data exist:
  take the published class twist and contragredients, and the L-polynomials and epsilon
  factor from `CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial` and
  `exists_isAutomorphicPairEpsilonFactor` (which rest on the proved
  `langlandsPairLFactorExistence` and `langlandsPairEpsilonFactorExistence`).
- `pairDataFactors_gamma`: the gamma factor of the data is `polynomialGammaExpression`.
- `hasRationalContinuation_pairDataFactors_gamma`: if `d` are twisted pair data and `G` is a
  certified automorphic gamma factor of `(πη, π')` for any twist `πη` of `π` by `η`, then the
  gamma factor of `pairDataFactors q d` has the rational continuation `G`. Proof: twist
  uniqueness identifies `πη`; `IsAutomorphicPairGammaFactor.unique` identifies `G` with the
  rational gamma expression of `d`; the dual L-polynomial is nonzero; then the published-shape
  lemma `hasRationalContinuation_polynomialGammaExpression` (module `Langlands.Automorphic.AssociatedGammaLocalLink`).
- `IsTwistedPairData.exists_gamma`: the data certify the rational gamma expression as the
  automorphic gamma factor of the twisted pair.
