# Reducing the L-factor characterization of the assembly to its ingredients

Author: Worker 1700.

This module proves Henniart 2002, Theorem 1.8 (printed p. 591; proof in §4.5,
printed p. 600, PDF p. 14) conditionally. The published proposition
`AssemblyLCharacterizationStatement F` is derived from five Library statements,
bundled in `AssemblyLCharacterizationIngredients F`. None of the five is proved
here. The module does not prove `AssemblyLCharacterizationStatement` outright.

## The ingredients

`AssemblyLCharacterizationIngredients F` (a `Prop`) is the conjunction of:

1. `AssemblyWellDefinedStatement F`.
2. `AssemblyBijectiveStatement F`.
3. `AssemblyLInheritanceStatement F`.
4. `RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement` at the
   universes `uF, uA, uA` (Henniart's Theorem 1.7(b)).
5. `AssemblySquareIntegrablePreimageStatement F`: a parameter assembled to an
   essentially square-integrable class is indecomposable (Henniart §§2.6–2.9).

All five use the same universes `uF, uP, uA` as the target.
`AssemblyExtendsStatement` is not an ingredient. The target's hypothesis that
`τ` extends `c0` supplies the zero-monodromy classes, and the proved
single-block witness of `AssemblyZeroMonodromyWitness` gives the values of
every assembly on them.

## Provenance (internal)

The bundle is an internal device: Henniart's §4.5 uses exactly these facts.
Well-definedness, bijectivity and L-inheritance come from §2 and Theorem 1.5,
the fourth is Theorem 1.7(b), and the fifth comes from the classification in
§§2.6–2.9.

## Lemmas

- `isSupercuspidal_rank_one`: every irreducible admissible representation of
  `GL_1(F)` is supercuspidal. The only block shape of rank one has one block:
  its length is at most 1 (`BlockShape.length_le`) and not 0 (an empty sum
  is not 1). A one-block parabolic is the whole group
  (`BlockShape.singleBlock_parabolic_eq_top`), so the Jacquet-module
  condition of `GeneralLinear.IsSupercuspidal` is vacuous.
- `extendsSupercuspidal_of_isAssemblyOf`: under ingredient 1, an assembly `c`
  of `c0` extends `c0` whenever some full map `τ` does. For each `σ`, `τ`
  provides a zero-monodromy class `E` of `σ`, and
  `assembly_apply_of_isZeroMonodromyOf` gives `c E = c0 σ`.
- `isIrreducibleWeilParameter_of_isSupercuspidal`: take `c0` surjective in
  every rank, `c` an extension of `c0` (`ExtendsSupercuspidal`) and `c`
  injective in every rank. If `c n D` is the class of a supercuspidal object
  `A`, then `D` is an irreducible Weil parameter. Bundle `A` as a
  `SupercuspidalRep` and choose a preimage `σ` under `c0`. The extension gives
  a zero-monodromy class `E` of `σ` with `c n E = c0 σ = c n D`, and
  injectivity gives `E = D`.
- `assembly_eq_of_lowerRankPairL`: Henniart's induction. Assume all five
  ingredients, a supercuspidal correspondence `c0`, a full map `τ` extending `c0`, a
  nontrivial additive character `ψ`, and the lower-rank hypothesis of the
  target for `τ` at `ψ`. Then every assembly `c` of `c0` equals `τ`.

## Proof of the induction

Fix an assembly `c`. By `extendsSupercuspidal_of_isAssemblyOf` and
ingredients 2 and 3, `c` extends `c0`, is bijective in every rank, and has the
L-inheritance property at `ψ`. The
correspondence `c0` supplies a self-dual measure `ν` for `ψ`
(`IsSupercuspidalCorrespondence.exists_selfDualMeasure`). By strong induction
on `k`, `c (k+1) D = τ (k+1) D` for every class `D` of rank `k + 1`:

- If `D` is an irreducible Weil parameter, `c` and `τ` agree on `D` because
  both extend `c0` (`ExtendsSupercuspidal.eq_on_irreducible`, Worker 422's
  `ZeroMonodromyExtension`).
- Otherwise, choose representatives `A` of `c D` and `B` of `τ D`. By the
  previous lemma, `A` is not supercuspidal. In rank 1 this contradicts
  `isSupercuspidal_rank_one`.
- In rank `n + 2`, apply `automorphicClass_eq_of_pole_order_tests` (Worker
  422's `AutomorphicPoleComparison`) with ingredient 4, `ψ` and `ν`. It
  remains to compare pole orders against each essentially square-integrable
  object `R` of rank `r + 1 ≤ n + 1`. Surjectivity of `c` gives `D'` with
  `c D' = [R]`. Ingredient 5 makes `D'` indecomposable, and the induction
  hypothesis gives `c D' = τ D'`. L-inheritance for `c` and the target's
  hypothesis for `τ` give two pair-L compatibilities of `(D, D')` with the
  same second image. `IsPairLCompatibleAt.same_pole_order` (Worker 422's
  `PairLCompatibilityComparison`) turns them into certified polynomials with
  equal pole orders, which are the required tests after rewriting by the
  representatives.

Every positive rank is `k.succPNat` for some `k`, which gives `c = τ`.

## Main theorem

`assemblyLCharacterization_of_ingredients` proves
`AssemblyLCharacterizationIngredients F → AssemblyLCharacterizationStatement F`.
Given `c0`, `τ`, `ψ` and the hypotheses of the target, the existence half of
ingredient 1 provides an assembly `c`. This is the published choice
`assemblyOfWellDefined F hwd c0` with its law
`assemblyOfWellDefined_isAssemblyOf` (`AssemblyConstruction`, Worker 864).
The induction gives `c = τ`, so
`τ` is an assembly of `c0`. Applied to any other assembly `c'`, it gives
`c' = τ`. The uniqueness half of ingredient 1 is used only pointwise, on
zero-monodromy classes.
