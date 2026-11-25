# Reducing the local pairing premise to duality and factor invariance

Module: `Langlands.Global.RankinSelberg.RealStandardPairingReduction` (namespace
`Langlands.Global.RankinSelbergGlobal`, helpers in
`Langlands.Global.RankinSelbergGlobal.RealStandardPairingReduction`).

This module proves that the two local statements of
`Langlands.Global.RankinSelberg.RealStandardPairingPremises`, D
(`RealStandardDualPairingStatement`, duality) and U (`RealStandardIntertwinerPairLStatement`,
factor invariance), imply the local pairing premise `RealStandardPairingPairLStatement` (L_R)
of `Langlands.Global.RankinSelberg.RealPlaceContragredientPremises`.

This module does not prove D, U or L_R on its own. It proves L_R only from D and U, which are
hypotheses of its theorem. The Library proves D as `realStandardDualPairing` in
`Langlands.Global.RankinSelberg.RealStandardDualPairingProof` and U as
`realStandardIntertwinerPairL` in
`Langlands.Global.RankinSelberg.RealStandardIntertwinerPairLProof`. This module neither imports
nor uses these proofs.

The module contains

* the proposition `RealStandardPairingPairLReductionStatement`, the implication D → U → L_R.
  It is the entry declaration;
* the theorem `realStandardPairingPairLReduction`, which proves that proposition;
* helper lemmas and one helper definition in the namespace
  `Langlands.Global.RankinSelbergGlobal.RealStandardPairingReduction`.

## Notation

As in `RealStandardPairingPremises.md`: `I(ds) = realStandardKFinite n ds` is the space of
`O(n)`-finite vectors of the Library's real standard module of the block list `ds`, with right
translation `realStandardRep n ds` by `O(n) = Matrix.unitaryGroup (Fin n) ℝ` and the
right-derivative action `realStandardLie n ds` of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`.
`IsRealStandardInvariantPairing n ds es P` (from `RealPlaceContragredientPremises`) says that the
bilinear form `P : I(ds) → I(es) → ℂ` is invariant under `O(n)` and satisfies
`P(X f, h) + P(f, X h) = 0` for real matrices `X`. `kDual (realStandardRep n ds)` is the
Library's `O(n)`-finite dual (`KFiniteDual`), with the dual translation `kDualRep` and the dual
Lie action `RealContragredient.dualLie`.

## Statement

`RealStandardPairingPairLReductionStatement` is

`RealStandardDualPairingStatement → RealStandardIntertwinerPairLStatement →
RealStandardPairingPairLStatement`.

L_R says: if `ds`, `dds` have rank `n`, `I(ds)` and `I(dds)` are irreducible, and some nonzero
`P` satisfies `IsRealStandardInvariantPairing n ds dds P`, then for every list `xs` of real
blocks the pair `L`-factors of `dds` and of `ds.map dualBlock` against `xs` have the same
denominator, with `xs` in the second slot and with `xs` in the first slot. The reduction is
proved by `realStandardPairingPairLReduction`.

## The implemented proof

Helpers (namespace `RealStandardPairingReduction`), for an invariant form
`P : I(ds) → I(es) → ℂ` with proof `hP`:

- `flip_rep`: `P(·, k h)` is the dual translate `(realStandardRep n ds).dual k (P(·, h))`. It is
  the `O(n)`-invariance applied to `k⁻¹ f` and `h`.
- `flip_lie`: `P(f, Y h) = -P(Y f, h)` for every `Y ∈ ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. The hypothesis gives it
  for `Y = 1 ⊗ X`; induction on the tensor product extends it, using `c ⊗ X = c • (1 ⊗ X)`.
- `isFiniteVector_flip`: `P(·, h)` is an `O(n)`-finite functional. Its orbit span lies in the
  image under `P.flip` of the orbit span of `h`, which is finite-dimensional because `I(es)` is
  an `O(n)`-finite module (`isRealGKModule_realStandardModule`).
- `toKDual hP : I(es) → kDual (realStandardRep n ds)`, `h ↦ P(·, h)`, with values in the
  Library's `O(n)`-finite dual (`KFiniteDual.kDual`). `toKDual_apply_apply` evaluates it.
  `toKDual_rep` and `toKDual_lie` say that it intertwines `realStandardRep n es` with `kDualRep`
  and `realStandardLie n es` with the dual Lie action `RealContragredient.dualLie`.
- `toKDual_injective`: if every nonzero `h` has some `f` with `P f h ≠ 0`, `toKDual hP` is
  injective.
- `range_toKDual_rep`, `range_toKDual_lie`: the range of `toKDual hP` is stable under both dual
  actions.
- `isRealStandardIntertwiner_of_map`: a linear map `I(es) → I(es')` that commutes with right
  translation by `O(n)` and with the right derivatives along real matrices satisfies
  `IsRealStandardIntertwiner`. The proof unfolds `isRealStandardIntertwiner_id`, which supplies
  the membership proofs of the translated and differentiated vectors.

Proof of `realStandardPairingPairLReduction`. Let `ds`, `dds` have rank `n`, let `I(ds)` and
`I(dds)` be irreducible, and let `P : I(ds) → I(dds) → ℂ` be a nonzero invariant form. Put
`ds' = ds.map dualBlock`, which has rank `n` by `RealLocalJacquet.realRank_map_dualBlock`.

1. D gives a form `Q : I(ds) → I(ds') → ℂ` whose first two clauses are, by definition,
   `IsRealStandardInvariantPairing n ds ds' Q`, and which separates `I(ds')`.
2. The `O(n)`-finite dual of `I(ds)` is irreducible by the Library's
   `RealContragredient.isIrreducible_kDual`, using the admissibility theorem
   `realStandardAdmissible`.
3. `toKDual hQ` is injective by `toKDual_injective`. Its range is a stable subspace of the
   irreducible dual. It is not `⊥`, since `I(ds')` is nonzero (`realStandardNontrivial`) and the
   map is injective. So the range is `⊤`, and `toKDual hQ` is a linear equivalence `E`
   (`LinearEquiv.ofBijective`).
4. `I(ds')` is irreducible: it is nonzero, and for a stable subspace `W`, the image of `W` under
   `toKDual hQ` is stable by `toKDual_rep` and `toKDual_lie`, hence `⊥` or `⊤`. Since the map is
   injective, `W = comap (map W)` is `⊥` or `⊤`.
5. `T = E⁻¹ ∘ toKDual hP : I(dds) → I(ds')` intertwines both actions, because `toKDual hP` and
   `toKDual hQ` do. By `isRealStandardIntertwiner_of_map` it is an `IsRealStandardIntertwiner`
   map. It is nonzero: if `T = 0` then `toKDual hP = 0`, so `P f h = 0` for all `f` and `h`,
   contradicting `P ≠ 0`.
6. U applied to `es = dds`, `es' = ds'` and `T` gives, for every `xs`, the equalities of the
   denominators of `realPairLFactor dds xs` and `realPairLFactor ds' xs`, and of
   `realPairLFactor xs dds` and `realPairLFactor xs ds'`. These are the two conclusions of L_R.

Of `P`, the proof uses only invariance and `P ≠ 0`. It does not need `P` to separate either
side. The irreducibility of `I(dds)` is used only as a hypothesis of U. The irreducibility of
`I(ds')` that U also needs is proved in step 4.

The theorem's only premises are D and U. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance and status

Both items, the proposition `RealStandardPairingPairLReductionStatement` and the theorem
`realStandardPairingPairLReduction`, are internal to this Library, and so are the helpers.

* The proposition is the implication among three Library propositions: D and U (module
  `RealStandardPairingPremises`) and L_R (module `RealPlaceContragredientPremises`). It is not a
  statement from a source. It is the entry declaration of the proved theorem.
* The theorem's argument is the usual Schur-type one. A separating invariant pairing identifies
  `I(ds.map dualBlock)` with the `O(n)`-finite dual of `I(ds)`. Any nonzero invariant pairing
  then gives a nonzero intertwiner into that dual. The proof is derived from the Library results
  `RealContragredient.isIrreducible_kDual`, `realStandardAdmissible`, `realStandardNontrivial`,
  `isRealGKModule_realStandardModule`, `isRealStandardIntertwiner_id` and
  `RealLocalJacquet.realRank_map_dualBlock`, and cites no literature.

The mathematical content of D and U is discussed in `RealStandardPairingPremises.md`, with their
sources (Knapp 1994, Knapp 1986 Chapter VII). L_R is discussed in
`RealPlaceContragredientPremises.md`.

The reduction is an intermediate step toward `RealPlaceContragredientPairLStatement`.
With `realPlaceContragredientPairLReduction` from
`Langlands.Global.RankinSelberg.RealPlaceContragredientReduction`, that statement follows from the
Library's global irreducibility statement and from D and U, as
`realPlaceContragredientPairLReduction hG (realStandardPairingPairLReduction hD hU)`.

To repeat: this module does not prove D, U or L_R. It proves only that D and U together imply
L_R.
