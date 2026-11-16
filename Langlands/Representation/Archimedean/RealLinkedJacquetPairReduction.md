# The linked Jacquet functional from pairs of blocks, swaps and induction in stages

Lean module: `Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction`.

## Notation

`I_n(ds)` is the `(𝔤𝔩_n(ℝ), O(n))`-module `(realStandardRep n ds, realStandardLie n ds)` on
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)`, the `O(n)`-finite functions
of the Library's real standard module of the list `ds` of real blocks. A block is
`RealBlock.character c` (rank `1`) or `RealBlock.induced d` (rank `2`, weight `d.weight`);
`realBlockExponent` is the real part of its exponent. `IsRealBlockNondegenerate x` means that `x`
is a character or an induction block of nonzero weight. `AreRealBlocksUnlinked x y` (no Mœglin
datum of `x` is linked to one of `y`), `IsRealMoeglinUnlinked ds`, `IsRealLanglandsOrdered ds`
(real exponents non-increasing), `IsRealStandardIntertwiner`, `realBlockExpand` and
`RealUnlinkedSwapStatement` are the Library's.

## The conclusion

`RealLinkedJacquetFunctionalExists n ds` is the existence of

* a nonzero `ℂ`-linear functional `ℓ` on `I_n(ds)`,
* exponents `a : Fin n → ℂ` and signs `e : Fin n → Fin 2` with
  `IsRealJacquetFunctional n (realStandardRep n ds) (realStandardLie n ds) ℓ a e`
  (`ℓ` kills `π(1 ⊗ X)` for strictly upper triangular real `X`, `π(1 ⊗ E_jj)` acts on `ℓ` by
  `a_j`, and the sign reflection at `j` acts on `ℓ` by `(-1)^{e_j}`),
* a position `p` with `p + 1 < n` and `k : ℕ` with `a_p - a_{p+1} = 1 - k`,
* such that `ℓ(π(1 ⊗ E_{p+1,p})^k v) = 0` for every `v`, where `E_{p+1,p}` is
  `Matrix.single ⟨p + 1, hp⟩ ⟨p, _⟩ 1`.

This is exactly the conclusion of the statement `RealLinkedJacquetFunctionalStatement` (S2) of
Task 7070 (module `RealLinkedJacquetFunctional`, accepted candidate 1cd3f2d0, not yet in the
Library), whose `lowerRootMatrix n p hp` is by definition
`Matrix.single ⟨p + 1, hp⟩ ⟨p, Nat.lt_of_succ_lt hp⟩ 1`. The predicate is restated here so that this
module depends only on the Library.

## Twisting blocks

* `realBlockTwist c x`: the block `x` twisted by `|det|^c`, `c : ℝ`. The exponent `t` becomes
  `t + c`. The parity of a character and the weight of an induction block do not change. It agrees
  with `RealLeviSlices.twistBlock` of the staged candidates of another task.
* `MoeglinDatum.twist c`: the Mœglin datum with exponent `s + c`.
* Proved lemmas: twisting preserves the rank (`realBlockTwist_rank`, `realRank_map_realBlockTwist`)
  and nondegeneracy. It adds `c` to the real exponent (`realBlockExponent_twist`). It commutes with
  `realBlockMoeglinData` (`realBlockMoeglinData_twist`). Linkedness depends only on differences of
  exponents, so twisting both blocks keeps their linkedness (`MoeglinDatum.isLinked_twist`,
  `areRealBlocksUnlinked_twist`).

## The statements (not proved here)

1. `RealLinkedJacquetFunctionalInStagesStatement` (Stages). Let `pre ++ core ++ post` have
   total rank `n`, and let `c = (realRank post - realRank pre)/2`. If
   `RealLinkedJacquetFunctionalExists (realRank core) (core.map (realBlockTwist c))` holds, then
   `RealLinkedJacquetFunctionalExists n (pre ++ core ++ post)` holds.
2. `RealSwapInjectiveIntertwinerSurjectiveStatement` (SwapSurj). Let `pre ++ x :: y :: post` have
   total rank `n`. Every injective `ℂ`-linear `T : I_n(pre ++ x :: y :: post) →
   I_n(pre ++ y :: x :: post)` that is an intertwiner (`IsRealStandardIntertwiner`) is
   surjective. The blocks `x`, `y` are arbitrary.
3. `RealPairLinkedJacquetFunctionalStatement` (Pair). Let `x`, `z` be nondegenerate blocks with
   `realBlockExponent z ≤ realBlockExponent x` and `¬ AreRealBlocksUnlinked x z`. Then
   `RealLinkedJacquetFunctionalExists (realRank [x, z]) [x, z]` holds.
4. The four kinds of Pair, each on its own group:
   * `RealCharacterPairLinkedJacquetFunctionalStatement` (CC): two characters `c`, `d`, on `GL_2(ℝ)`;
   * `RealInducedCharacterLinkedJacquetFunctionalStatement` (IC): `[induced d, character c]` with
     `d.weight ≠ 0`, on `GL_3(ℝ)`;
   * `RealCharacterInducedLinkedJacquetFunctionalStatement` (CI): `[character c, induced d]` with
     `d.weight ≠ 0`, on `GL_3(ℝ)`;
   * `RealInducedInducedLinkedJacquetFunctionalStatement` (II): `[induced d, induced e]` with
     nonzero weights, on `GL_4(ℝ)`.

   Each has the hypotheses of Pair for its kind: the second block has real exponent at most that
   of the first, and the two blocks are linked.
5. `RealLinkedJacquetFunctionalReductionStatement` is the implication
   Stages → `RealUnlinkedSwapStatement` → SwapSurj → Pair → (for all `n`, `ds` with
   `realRank ds = n`, `IsRealLanglandsOrdered ds` and `¬ IsRealMoeglinUnlinked ds`,
   `RealLinkedJacquetFunctionalExists n ds`). Its conclusion is S2.

## Proved results

* `realPairLinkedJacquetFunctional_of_kinds`: CC, IC, CI and II imply Pair. The proof is a case
  split on the kinds of `x` and `z`. `realRank [x, z]` reduces to `2`, `3`, `3` or `4`.
* `realLinkedJacquetFunctionalReduction : RealLinkedJacquetFunctionalReductionStatement`.

Auxiliary results used by the proof:

* `RealSurjectiveIntertwinerExists n ds es`: there is a surjective intertwiner `I_n(ds) → I_n(es)`.
  It is reflexive and transitive. It holds when the two standard modules are equal (`of_eq`, via
  the identity on functions).
* `IsRealStandardIntertwiner.map_pow_realStandardLie`: an intertwiner carries `π(Y)^k` to `π(Y)^k`.
* `RealLinkedJacquetFunctionalExists.of_surjective`: if `T : I_n(ds) → I_n(es)` is a surjective
  intertwiner and `ℓ` works for `es`, then `ℓ ∘ T` works for `ds` with the same `a`, `e`, `p` and
  `k`. Surjectivity gives `ℓ ∘ T ≠ 0`.
* `realSurjectiveIntertwinerExists_moveLeft`: let every block `w` of `mid` have
  `realBlockExponent z ≤ realBlockExponent w` and `AreRealBlocksUnlinked w z`. Then
  Swap and SwapSurj give a surjective intertwiner from `I_n(pre ++ mid ++ z :: post)` to
  `I_n(pre ++ z :: mid ++ post)`. The proof is by induction on `mid`: move `z` past the last blocks
  first, then exchange the first block `w` of `mid` with `z`.
* Expansion of weight-zero blocks: `realStandardModule_append_flatMap_expand` (iterating the
  Library's `realStandardModule_append_expand`), `realRank_flatMap_expand`,
  `realMoeglinData_flatMap_expand`, and `isRealMoeglinUnlinked_of_pairwise`. The last says that a
  list of nondegenerate blocks whose blocks are pairwise unlinked is Mœglin-unlinked.
* `exists_split_of_not_pairwise`: if a list is not `R`-pairwise, it splits as
  `pre ++ x :: (mid ++ y :: post)` with `¬ R x y` and `R w y` for every `w ∈ mid`. The proof is by
  induction. If the tail is `R`-pairwise, take `x` the head and `y` the first element not
  `R`-related to it; the blocks between them are related to `y` because the tail is pairwise.

### Proof of `realLinkedJacquetFunctionalReduction`

Let `ds` have rank `n`, be Langlands-ordered and have a linked pair of Mœglin data.

1. Let `es = ds.flatMap realBlockExpand`. It replaces every induction block of weight `0` by its
   two characters with the same exponent. `es` has the same standard module, the same rank and the
   same Mœglin data as `ds`. All its blocks are nondegenerate, and it is Langlands-ordered, because
   an expanded block keeps the exponent of its block. Its blocks are not pairwise unlinked, by
   `isRealMoeglinUnlinked_of_pairwise`.
2. `exists_split_of_not_pairwise` with `R = AreRealBlocksUnlinked` gives
   `es = pre ++ x :: (mid ++ z :: post)`, with `x`, `z` linked and every `w ∈ mid` unlinked to `z`.
   Langlands order gives `Re t(z) ≤ Re t(x)` and `Re t(z) ≤ Re t(w)` for `w ∈ mid`.
3. `realSurjectiveIntertwinerExists_moveLeft` gives a surjective intertwiner
   `I_n(es) → I_n(pre ++ [x, z] ++ (mid ++ post))`.
4. Let `c = (realRank (mid ++ post) - realRank pre)/2`. Pair applies to the twisted pair
   `[x', z']`, where `x' = realBlockTwist c x` and `z' = realBlockTwist c z`. They are
   nondegenerate, still ordered, and still linked. `realRank [x', z'] = realRank [x, z]`. Stages
   with core `[x, z]` gives `RealLinkedJacquetFunctionalExists n (pre ++ [x, z] ++ (mid ++ post))`.
5. Pull back along the surjection of step 3 and along the identity `I_n(ds) = I_n(es)`
   (`of_surjective`).

The module compiles with no errors or warnings and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Why the statements are expected to be true

* **Stages.** Let `ψ ↦ ψ̃`, where `ψ̃(g) = ψ(diag(1_{pre}, g, 1_{post}))`, be restriction to the
  block `GL_r(ℝ)` at the positions of `core`. `principalSeriesCharacter` contains
  `|a_i|^{(n-1)/2 - i}`. At the positions `i = rank pre + j` of the core this is
  `|a_i|^{(r-1)/2 - j} · |a_i|^{(rank post - rank pre)/2}`. The block Fourier conditions are
  conditions on left rotations inside the core block. So restriction maps
  `realStandardModule n (pre ++ core ++ post)` into `realStandardModule r (core.map
  (realBlockTwist c))`, and `O(n)`-finite functions to `O(r)`-finite functions.

  Let `ℓ'` be a functional for the twisted core. Define `ℓ(f) = ℓ'(f̃)`. Then `ℓ` is a Jacquet
  functional. Let `X` lie in the unipotent radical of the parabolic subgroup, or be strictly upper
  triangular in the `pre` or `post` block. Then `f` is left invariant under the corresponding
  one-parameter subgroup, so `ℓ(π(X)f) = 0`. The diagonal elements and sign reflections in the `pre`
  and `post` blocks act on `ℓ` by the principal series character. The derivatives and sign
  reflections in the core block commute with restriction. So the exponents of `ℓ` are `a'` on the
  core positions, and the core position `p` becomes `p + rank pre`. Nonvanishing of `ℓ` follows from surjectivity of restriction onto
  the `O(r)`-finite functions (extension through the Iwasawa decomposition). This is the
  restriction to the Levi factor in induction in stages (Knapp 1986, Ch. VII).
* **SwapSurj.** The restriction of `I_n(pre ++ x :: y :: post)` to `O(n)` is induced from
  `O(n) ∩ M`, where `M` is the Levi subgroup of the blocks. The inducing representation depends
  only on the parities and weights of the blocks. Exchanging `x` and `y` conjugates it by a
  permutation matrix in `O(n)`. Left translation by that matrix identifies the two restrictions
  to `O(n)`. So both modules have the same `O(n)`-multiplicities, and these are finite. An
  injective `O(n)`-map is then bijective on every isotypic component, hence surjective.
* **Pair and its four kinds.** Each kind is the case `ds = [x, z]` of S2, by the definitional
  equality above. The justification of S2, with its sources (Mœglin 1997; Knapp 1986, Theorem
  7.24; Bernstein–Gelfand 1980, Theorem 4.1), is in `RealLinkedJacquetFunctional.md`. CC follows
  from the character case `RealCharacterLinkedJacquetFunctionalStatement` (candidate e874e0ce),
  for which Worker 5731 has a draft proof. IC, CI and II are the cases on `GL_3(ℝ)` and `GL_4(ℝ)`.
  These are the groups to which Mœglin (1997, p. 165) reduces Speh's criterion.

## Provenance

The reduction is internal to Task 7070. It follows the pattern of Mœglin's reduction of
Theorem 10b to `GL(a)`, `a = 2, 3, 4` (Mœglin 1997, p. 165), and the Library's
`RealUnlinkedSwapReduction`. First, choose a linked pair with no block in between linked to the
second block. Then move the second block next to the first by unlinked swaps. Finally, restrict to
the pair by induction in stages. No statement is quoted from a source.
