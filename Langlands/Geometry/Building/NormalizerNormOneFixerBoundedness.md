# Boundedness of the norm-one stabilizer of an apartment point in `N(F)`

This module bounds the normalizer part of a singleton sharp fixer, as in the
second half of the proof of KP Corollary 7.3.14. It works with the actual
building data `B : ValuationBuildingData G`, at arbitrary universe `u`. Here
`F` is a nonarchimedean local field, `G` is the connected reductive group of
`B`, and `i : S → G` is its maximal split torus. `N(F) = normalizerPoints B.i`
and `Z(F)` are the rational points of the normalizer and of the centralizer
`B.centralizer.Z` (embedded by `j = B.centralizer.j`). `G(F)^1` and `Z(F)^1` are
the norm-one subgroups `rationalCommonNormKernel`, the common kernels of the
valuations `ω ∘ χ` of all rational characters `χ`.

The only premise of the boundedness results is that `Z(F)^1` (or its image
under `j`) is bounded. No apartment axioms, Bruhat decomposition or boundedness
of stabilizers are assumed.

## A linear-algebra lemma on split tori

`RealTorusSpace.eq_zero_of_eval_eq_zero_of_span`: let `T` be a split torus over
a field and `R` a set of characters whose rationalizations span
`ℚ ⊗ X*(T)`. A real cocharacter `v ∈ V(T) = ℝ ⊗ X_*(T)` on which every
`χ ∈ R` evaluates to `0` is `0`.

Proof: `v` gives the `ℚ`-linear form `φ = (pair T · v) ∘ toReal` on
`ℚ ⊗ X*(T)`. It kills the spanning set `toRat '' R`, so it is zero, so
`eval T χ v = 0` for every character `χ`. Hence `(pair T).flip v` vanishes on
every pure tensor `r ⊗ χ = r • (1 ⊗ χ)` of `ℝ ⊗ X*(T)`, so it is zero. The pairing is
perfect for a split torus (`isPerfPair_of_isSplitTorus`), so `v = 0`.

## The norm-one stabilizer

- `normOneNormalizerStabilizer B x` (definition), for `x : B.Apartment`: the
  subgroup `G(F)^1 ⊓ (stabilizer of x in N(F)).map (subtype)` of `G(F)`. That
  is, `N(F)^1_x = {n ∈ N(F) | n ∈ G(F)^1, n · x = x}`, where `N(F)` acts on the
  apartment by the building data's action.
- `mem_normOneNormalizerStabilizer`: `g` lies in it if and only if
  `g ∈ G(F)^1` and `g = n` for some `n : N(F)` with `n • x = x`.

It is meant to contain the normalizer part of the sharp fixer of `{x}`: the sharp
fixer of a nonempty set lies in `G(F)^1` under the topology-compatibility premise
(the Library's `sharpFixer_le_rationalCommonNormKernel`). That containment is not
stated in this module.

## Elements of `Z(F)` fixing `x`

- `torusCharacterRestrict_eq_characterRestriction`: restricting a rational
  character of `G` to `S` equals restricting it to `Z` along `j` and then to `S`
  along `s = B.centralizer.s`. This follows from `s ≫ j = i`
  (`CentralizerDatum.comp_eq`) and `characterRestrict_comp`.
- `eval_torusCharacterRestrict_translation`: for `z ∈ Z(F)` and a rational
  character `χ` of `G`, the restriction of `χ` to `S` takes the value
  `-ω(χ(j z))` on the translation vector `ν(z) = (B.translation z).toAdd`.
  This combines the previous lemma with the Library's
  `eval_centralizerTranslation` and `rationalCharacterEval_characterRestrict`.
- `mem_rationalCommonNormKernel_of_smul_eq`: if `z ∈ Z(F)`, `j z ∈ G(F)^1`, and
  `z` (as an element of `N(F)`) fixes some point `x`, then `z ∈ Z(F)^1`.

  Proof: by `IsOmegaCompatible.smul_eq_vadd`, `z` acts on the apartment as
  translation by the class of `ν(z)` in `TranslationSpace B.i = V(S)/V(S)^Φ`.
  Fixing `x` forces this class to be zero, so `ν(z)` lies in the root
  annihilator: every relative root vanishes on it. Every restricted rational
  character `χ|_S` of `G` also vanishes on it, because `ω(χ(j z)) = 0` for
  `j z ∈ G(F)^1`. The relative roots and the restricted characters together span
  `ℚ ⊗ X*(S)`. This is the Library theorem
  `relativeRootsRestrictedCharactersSpan`, proved with no further premise. The
  split-torus lemma then gives `ν(z) = 0`. Since `ker ν = Z(F)^1`
  (`centralizerTranslation_ker`), `z ∈ Z(F)^1`.

## Covering by translates and boundedness

- `normOneNormalizerStabilizer_subset_iUnion`: there is a function
  `r : relativeWeylGroup B.i → G(F)` such that `N(F)^1_x` is contained in
  `⋃ w, r w • j(Z(F)^1)`. Here `relativeWeylGroup B.i = N(F)/Z(F)`.

  Proof: for each class `w`, `r w` is some element `m` of `N(F)^1_x` in the
  class `w` when one exists (by choice), and `1` otherwise. If `n ∈ N(F)^1_x`
  has class `w`, then `m` exists, and `m⁻¹ n` lies in `Z(F)` (the centralizer
  represents `torusCentralizer`, `B.centralizer.isRepresentedBy`), say
  `m⁻¹ n = j z`. Both `m` and `n` are in `G(F)^1` and fix `x`, so `j z ∈ G(F)^1`
  and `z` fixes `x`. By the previous lemma, `z ∈ Z(F)^1`, and
  `n = m · j z ∈ r w • j(Z(F)^1)`.
- `isAlgebraicallyBounded_normOneNormalizerStabilizer`: if the image
  `j(Z(F)^1)` is algebraically bounded in `G(F)` (KP Definition 2.2.1), then
  `N(F)^1_x` is algebraically bounded for every `x`.

  Proof: `relativeWeylGroup B.i` is finite, by the Library's
  `IsSplitTorus.finite_relativeWeylGroup_of_span` applied to the same span
  theorem. Each translate `r w • j(Z(F)^1)` is bounded
  (`IsAlgebraicallyBounded.smul_set`), a finite union of bounded sets is bounded
  (`isAlgebraicallyBounded_iUnion`), and subsets of bounded sets are bounded
  (`IsAlgebraicallyBounded.mono`). These lemmas come from
  `Langlands.BruhatTits.RationalPoints.BoundedSetOperations`.
- `isAlgebraicallyBounded_normOneNormalizerStabilizer_of_centralizer`: the same
  conclusion when `Z(F)^1` is bounded in `Z(F)` (with `Z` affine). Its image
  under `j` is bounded by `IsAlgebraicallyBounded.image_rationalPointsMap`.

## Provenance and scope

The definition and the results are internal helpers for KP Corollary 7.3.14
(Kaletha–Prasad 2023, §7.3, printed p. 251, PDF p. 282). KP argue that the image
of `N♯_{x,f}` in the affine Weyl group fixes `x`, so it contains no nontrivial
translation and is finite. Then boundedness of `Z(k)_0` gives boundedness of
`N♯_{x,f}`. This module follows that idea with two changes. It works with the
larger subgroup `N(F)^1_x`, defined by norm one and fixing `x` rather than by the
sharp fixer. And it uses `Z(F)^1` in place of `Z(k)_0`: by
`mem_rationalCommonNormKernel_of_smul_eq`, the elements of `Z(F)` in
`N(F)^1_x` lie in `Z(F)^1`, and this is the subgroup whose boundedness the
covering needs. Finiteness is taken from the finite group `N(F)/Z(F)` rather than from
the image in the affine Weyl group.

Boundedness of `Z(F)^1` is an explicit hypothesis. It is not proved here, and the
Library has no statement of it yet. Only the singleton `f = 0` situation of the
corollary is addressed, and the module does not mention the sharp fixer itself.
