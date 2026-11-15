# The local step of Murre's induction from its parts

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepReduction`
proves that Steps 1, 2a and 2b, as stated in
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts`, imply
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepStatement`. It is a
conditional reduction: the steps themselves are not proved here. It also proves
the dimension estimates needed to apply the induction hypothesis.

## Results

- `ringKrullDim_stalk_puncturedSpectrum_lt R s`: for a local noetherian ring
  `R : CommRingCat.{u}` and a point `s` of the open subscheme
  `puncturedSpectrum R`, the local ring of `puncturedSpectrum R` at `s` has
  Krull dimension `< ringKrullDim R`.
- `ringKrullDim_stalk_le_zero_of_isArtinianRing A s`: for an artinian ring
  `A : CommRingCat.{u}` and a point `s : Spec A`, the local ring of `Spec A`
  at `s` has Krull dimension `≤ 0`.
- `ringKrullDim_adicCompletion_le R`: for a local noetherian ring `R`,
  `ringKrullDim (AdicCompletion (maximalIdeal R) R) ≤ ringKrullDim R`.
- `isArtinianRing_quotient_maximalIdeal_pow A k`: for a local noetherian ring
  `A` and `k : ℕ`, the ring `A ⧸ maximalIdeal A ^ (k + 1)` is artinian.
- `unramifiedRepresentable_puncturedSpectrum hn R hR F hF`: if
  `hn : MurreDimensionBound.{u, v} n`, `R` is a local noetherian ring with
  `hR : ringKrullDim R ≤ n` and `hF : MurreConditions F`, then
  `UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F)`.
- `unramifiedRepresentable_of_isArtinianRing hn hn0 A F hF`: if
  `hn : MurreDimensionBound.{u, v} n` with `hn0 : n ≠ 0`, `A` is an artinian
  ring and `hF : MurreConditions F` for `F` on `Over (Spec A)`, then
  `UnramifiedRepresentable F`.
- `murreLocalStep_of_parts : MurreLocalStepPartsStatement.{u, v} →
  MurreLocalStepStatement.{u, v}`.

## Proofs

`ringKrullDim_stalk_puncturedSpectrum_lt`. By Mathlib's
`ringKrullDim_stalk_eq_coheight`, the dimension of the local ring at `s` is the
coheight of `s` in the specialization order of `puncturedSpectrum R`. By
`coheight_eq_of_isOpenImmersion`, applied to the open immersion
`(puncturedSpectrum R).ι`, this is the coheight of its image `x` in `Spec R`,
which by `idealHeight_eq_coheight` is the height of the prime `x.asIdeal`.
The dimension of `R` is the height of its maximal ideal
(`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`). Since `x` is not the
closed point, `x.asIdeal` is a prime strictly contained in `maximalIdeal R`.
The maximal ideal has finite height (a local noetherian ring has finite
dimension), so `Ideal.height_strict_mono_of_isPrime_of_isPrime` gives the
strict inequality of heights.

`ringKrullDim_stalk_le_zero_of_isArtinianRing`. As above, the dimension of the
local ring at `s` is the height of `s.asIdeal`, which is at most
`ringKrullDim A` (`Ideal.height_le_ringKrullDim_of_isPrime`). An artinian ring
has dimension `≤ 0` (Mathlib's instance `Ring.KrullDimLE 0 A` and
`Ring.krullDimLE_iff`).

`ringKrullDim_adicCompletion_le`. Write `m` for the maximal ideal of `R` and
`m̂` for that of `R̂ = AdicCompletion m R`; both dimensions are heights of
maximal ideals. The map `R → R̂` is a local homomorphism (Mathlib instance), so
`m̂` lies over `m`. Mathlib's `Ideal.height_le_height_add_of_liesOver` (`R̂` is
noetherian by the Library instance
`Langlands.AlgebraicGeometry.Deformation.AdicCompletionNoetherian.instIsNoetherianRing`)
gives `height m̂ ≤ height m + height (m̂ (R̂ ⧸ m R̂))`. By
`AdicCompletion.maximalIdeal_eq_map`, `m R̂ = m̂`, so the last ideal is the
zero ideal of the field `R̂ ⧸ m̂` (`Ideal.map_quotient_self`), of height `0`
(`Ideal.height_bot`).

`isArtinianRing_quotient_maximalIdeal_pow`. Mathlib's
`IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing` reduces it
to `m` being a minimal prime over `m^(k+1)`: `m^(k+1) ≤ m`
(`Ideal.pow_le_self`), and every prime `q ⊇ m^(k+1)` contains `m`
(`Ideal.IsPrime.le_of_pow_le`).

`unramifiedRepresentable_puncturedSpectrum`. Apply `hn` to the locally
noetherian scheme `puncturedSpectrum R` (an open subscheme of the noetherian
`Spec R`; Mathlib instances) and the presheaf
`baseChange (puncturedSpectrum R).ι F`. It satisfies `MurreConditions` by the
Library theorem `murreBaseChange`, and its local rings have dimension
`< ringKrullDim R ≤ n` by `ringKrullDim_stalk_puncturedSpectrum_lt`.

`unramifiedRepresentable_of_isArtinianRing`. Apply `hn` to `Spec A`, which is
locally noetherian (an artinian commutative ring is noetherian). Its local
rings have dimension `≤ 0 < n`.

`murreLocalStep_of_parts`. Let `h1`, `h2a`, `h2b` be Steps 1, 2a and 2b, let
`n : ℕ` with `hn : MurreDimensionBound n`, let `R` be local noetherian with
`ringKrullDim R = n`, and let `F` satisfy `MurreConditions F`.

- If `n = 0`, then `R` has dimension `≤ 0` and is noetherian, hence artinian
  (`isArtinianRing_iff_krullDimLE_zero`); Step 1 `h1` gives the claim.
- If `n > 0`, let `R̂ = AdicCompletion (maximalIdeal R) R`, as an object of
  `CommRingCat.{u}`. It is local, noetherian and complete for its maximal ideal
  (Mathlib instances in `Mathlib.RingTheory.AdicCompletion.LocalRing` and the
  Library noetherian instance), and `ringKrullDim R̂ ≤ n` by
  `ringKrullDim_adicCompletion_le`. The base change
  `F̂ = baseChange (completionMap R) F` satisfies `MurreConditions` by
  `murreBaseChange`. Step 2b `h2b` reduces the claim to two hypotheses:
  representability over the punctured spectrum of `R`, which is
  `unramifiedRepresentable_puncturedSpectrum` for `R`; and representability of
  `F̂`. The latter is Step 2a `h2a` for `R̂` and `F̂`, whose two hypotheses are
  `unramifiedRepresentable_puncturedSpectrum` for `R̂` and `F̂`, and, for each
  `k`, `unramifiedRepresentable_of_isArtinianRing` for the artinian ring
  `R̂ ⧸ m̂^(k+1)` (`isArtinianRing_quotient_maximalIdeal_pow`) and the base
  change of `F̂` along `maximalIdealPowQuotientMap R̂ k`, which satisfies
  `MurreConditions` by `murreBaseChange`.

Murre obtains the representability over `Spec (R̂ ⧸ m̂^(k+1))` from Step 1;
here it comes from the induction hypothesis, which applies since these
artinian bases have dimension `0 < n`.
