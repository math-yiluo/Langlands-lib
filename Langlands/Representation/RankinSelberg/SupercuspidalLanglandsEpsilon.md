# Langlands-data epsilon factors of supercuspidal pairs

This module shows that a square-integrable Langlands datum presenting an
irreducible supercuspidal representation has exactly one block, and that the
block is equivalent to the representation. As a consequence, on pairs of
supercuspidal representations the epsilon relation
`RankinSelberg.IsLanglandsPairEpsilonFactor`, which is defined through
Langlands data, gives the JPSS epsilon relation
`RankinSelberg.IsPadicSymmetricEpsilonFactor`. All results are proved
unconditionally. No classification, exhaustion or factor-existence
proposition is assumed.

## Declarations

Fix a prime `p`, `F : PadicField.{uF} p` and topological data `T`. Fix a
datum `d : SquareIntegrableLanglandsDatum.{uV, uF} T (r + 1)`, that is, an
ordered block shape of `r + 1` together with irreducible essentially
square-integrable blocks `π_i` in carrier universe `uV`.

- `PadicField.TopologicalData.IsEssentiallySquareIntegrable.isAdmissible`:
  an essentially square-integrable representation of `GL_n(F)` (with respect
  to `T`) is admissible. The definition supplies a real `s` for which the twist
  by `|det|^(-s)` is square-integrable, hence admissible. The determinant-norm
  real-power character has an open kernel, and admissibility is invariant
  under such twists (`isAdmissible_twist_iff`).
- `SquareIntegrableLanglandsDatum.singleBlockRepresentation` (definition): if
  `d.shape.length = 1`, this is the sole block `π_i` as a representation of
  the ambient `GL_{r+1}(F)`. It precomposes with the inverse of the
  entry-preserving `reindex` along `finCongr` of the rank equality
  `d.shape.singleBlock_size`. This is a rank cast only: the block's carrier
  and its action are unchanged.
- `SquareIntegrableLanglandsDatum.length_eq_one_of_isSupercuspidal`: if `J`
  (carrier universe `max uF uV`) satisfies `IsSupercuspidal` for `T`'s
  topology and `d.IsLanglandsQuotient J`, then `d.shape.length = 1`.
- `SquareIntegrableLanglandsDatum.nonempty_equiv_of_isSupercuspidal`: under
  the same hypotheses there is `h : d.shape.length = 1` and an actual
  representation equivalence from `d.singleBlockRepresentation h` to `J`.
- `RankinSelberg.isPadicRankEpsilonFactor_reindex_iff`: the natural-rank
  relation `IsPadicRankEpsilonFactor F ψ ν π σ e` is unchanged when `π` and
  `σ` are replaced by representations `π'`, `σ'` equivalent to their rank
  casts along `k = m` and `t = s`. The four carrier universes are independent.
- `RankinSelberg.IsLanglandsPairEpsilonFactor.isPadicSymmetricEpsilonFactor_of_isSupercuspidal`:
  for the canonical topological data of `F`, any `ψ`, any `ν`, ranks `r + 1`
  and `t + 1`, `π` and `σ` in carrier universes `max uF uV` and `max uF uW`,
  both `IsSupercuspidal`, and `e : ℂˣ × ℤ`,
  `IsLanglandsPairEpsilonFactor.{uF, uV, uW} F ψ ν π σ e` implies
  `IsPadicSymmetricEpsilonFactor F ψ ν π.representation σ.representation e`.

`IsSupercuspidal` is the Library predicate: admissibility, and zero Jacquet
coinvariants for every proper standard block parabolic and every conjugate of
its unipotent radical. Irreducibility of `J` comes from `IsLanglandsQuotient`.

## Proof

**One block.** Suppose that `d.shape.length ≠ 1`, and write `B = d.shape`.
The standard parabolic of `B` is proper. Otherwise
`CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top` makes the
block indices a subsingleton, so the length would be `0`, but the empty sum of
block sizes cannot be `r + 1`.
Let `σ_B` be the external tensor product of the blocks, a representation of
the Levi subgroup. It is admissible by `FiniteTensor.isAdmissible_external`,
because each block is admissible by the first lemma. The quotient `J` is
admissible because it is supercuspidal. The proved GL second adjointness
`Parabolic.normalizedSecondAdjointness`, at universes `uF, uV, max uF uV`,
gives a linear equivalence

`Hom_G(i_B σ_B, J) ≃ Hom_M(σ_B, oppositeJacquet T B J)`.

Here `i_B σ_B` is `T.normalizedParabolicInduced B σ_B`, which is the
representation of `d.induced`. The opposite Jacquet module is the Jacquet
module along the opposite unipotent radical, which is the conjugate of the
standard unipotent radical of the reversed shape `B.reverse` by
`B.reverseMatrix` (`BlockShape.reverse_unipotentSubgroup_map_conj`). The
reversed parabolic is still proper (`reverse_parabolic_ne_top_iff`), so
supercuspidality of `J` makes this Jacquet module a subsingleton. Therefore
the right side is zero, and the surjective quotient map `q : i_B σ_B → J` is
zero. That is impossible because the irreducible `J` is nontrivial
(`CuspidalSupport.QuasicuspidalEmbedding.nontrivial_of_isIrreducible`).

**The block is the quotient.** With one block,
`T.singleBlockNormalizedProductEquiv` identifies `d.induced` with the rank
cast of the block. Composing its inverse with `q` gives a surjective
intertwining map `f` from `d.singleBlockRepresentation h` to `J`. The source
is irreducible by `CuspidalSupport.isIrreducible_comp_mulEquiv_iff` and the
irreducibility of the block, so `f` is injective or zero
(`Representation.IsIrreducible.injective_or_eq_zero`). It is not zero because
`J` is nontrivial, so `IntertwiningMap.ofBijective f` is the equivalence.

**Rank transport.** In `isPadicRankEpsilonFactor_reindex_iff`, substituting
the rank equalities reduces the casts to the identity
(`reindex_finCongr_rfl`). The claim then follows from
`IsPadicRankEpsilonFactor.congr_equiv` (from `LanglandsFactorDescent`), which
allows different carrier universes.

**Epsilon factors.** Unfold `IsLanglandsPairEpsilonFactor` to obtain data `d`
and `d'` presenting `π` and `σ`, and the condition for all data. Applied to
`d` and `d'`, the condition gives the block factors `b i j`, certified by
`IsPadicRankEpsilonFactor`, whose product is `e`. Both data have one block,
with indices `i` and `j`. So `epsilonFactorProduct b` (complex coefficients
multiplied, exponents added) equals `b i j`
(`Fintype.prod_eq_single`, `Fintype.sum_eq_single`). The certificate for
`b i j` moves to `π` and `σ` through the two equivalences and the rank
transport lemma. `isPadicRankEpsilonFactor_succ` then converts the
natural-rank relation at ranks `r + 1` and `t + 1` into
`IsPadicSymmetricEpsilonFactor`.

## Provenance

This is internal content derived from the Library's definitions. The
motivation is Henniart, *Une caractérisation de la correspondance de Langlands
locale pour GL(n)*, Bull. Soc. Math. France 130 (2002), §2.8 (printed p. 596).
There, factors of pairs of irreducible representations are defined as
products of block factors over the Langlands data in `N[A_2] − {0}`. A
supercuspidal representation is its own one-element datum, so its factors are
the Jacquet–Piatetski-Shapiro–Shalika factors (Henniart's reference [6]). In
the Library, the epsilon relation through Langlands data quantifies over every
square-integrable datum presenting the representation. The theorem here shows
that each such datum of a supercuspidal representation has a single block,
equivalent to it. Henniart's proof of the corollary of Théorème 1.6 (§3.4,
printed p. 598) shows that `τ_n(σ)` is supercuspidal and then applies
Théorème 1.4, which compares epsilon factors of supercuspidal pairs. In the
Library, the pair factors of a full correspondence are certified through the
Langlands-data relation. The pair relation of a supercuspidal correspondence,
`Correspondence.IsSupercuspidalPairEpsilonFactor`, is
`IsPadicSymmetricEpsilonFactor` on representatives. This module supplies the
passage from the Langlands-data relation to `IsPadicSymmetricEpsilonFactor` on
supercuspidal pairs. The paper does not use second adjointness here: it treats
the point as part of the classification. The second-adjointness proof is this
module's own.

## Scope

The final theorem uses only the canonical topological data of `F`, as
`IsLanglandsPairEpsilonFactor` does. The datum lemmas hold for arbitrary
topological data `T`. Ranks are positive (`r + 1`, `t + 1`). The blocks of the
data have carrier universes `uV` and `uW`, as in `IsLanglandsPairEpsilonFactor`.
No self-duality condition on `ν` and no nontriviality condition on `ψ` is
added or used: the conclusion is the Library's JPSS relation at the same `ψ`
and `ν`. The converse direction, from JPSS factors back to the Langlands-data
relation, is not claimed.
