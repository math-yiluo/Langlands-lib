# Irreducibility of `ν^a A × ν^b A` from Zelevinsky 1.11(a)

Author: Worker 1032.

This internal helper of the proof of
`Langlands.Classification.JuxtaposedSegmentSocleReverseProductStructure`
(Zelevinsky 1980, Proposition 4.6, step (1), juxtaposed case) makes no literature
assertion of its own. It derives the irreducibility input of
`JuxtaposedSwapFromLibrary.segmentFactor_swap_of_isIrreducible'` from the Library
statement `TwoSupercuspidalNonadjacentProductIrreducible` (Zelevinsky 1980,
Proposition 1.11(a), first conjunct, in
`Classification.TwoSupercuspidalProductStructureStatement`), taken as the explicit
hypothesis `h11`. That statement is the first conjunct of the published
`TwoSupercuspidalProductStructure`. Its proof, `twoSupercuspidalProductStructure`
(module `Classification.TwoSupercuspidalProductStructureProof`), is already
imported by the published proof `segmentFullJacquetFormula` of Zelevinsky 3.1, which
this task's proof uses.

## Results

- `segmentSupercuspidalFactor_ne_twist_one`: for a supercuspidal representation `A`
  of `GL_r` and natural numbers with `b ≠ a + 1`, the rank-indexed class
  `⟨r, [ν^b A]⟩` differs from `⟨r, ν [ν^a A]⟩`, where `ν [·]` is
  `T.supercuspidalClassRealPowerTwist r 1`.
- `uniform_two_isIrreducible_of_nonadjacent`: assume
  `TwoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T`. For a supercuspidal
  representation `A` of `GL_r` and natural numbers with `b + 1 < a`, the product
  `ν^a A × ν^b A` along `BlockShape.uniform 2 r` is irreducible.

## Proofs

`segmentSupercuspidalFactor_ne_twist_one`: suppose the two classes are equal. The
second components of the dependent pairs are then equal. Let `β` be the cuspidal
datum `⟨r, hr, [A]⟩`. The class of `ν^b A` is that of `β.twist b`, and
`ν [ν^a A]` is that of `β.twist (1 + a)` by `CuspidalDatum.twist_twist`. So
`β.twist b = β.twist (a + 1)` as integral twists, and the Library's
`cuspidalDatum_integralTwist_injective` gives `b = a + 1`, contrary to the
assumption.

`uniform_two_isIrreducible_of_nonadjacent`: apply `h11` with `k = l = r`,
`ρ = ν^a A` and `ρ' = ν^b A` (as `segmentSupercuspidalFactor`s). Its two side
conditions are the first lemma for `b ≠ a + 1` and for `a ≠ b + 1`. Both follow from
`b + 1 < a`. This makes the product along `Shahidi.twoBlocks r r` irreducible. The
rank cast `r + r = 2 * r` sends `Shahidi.twoBlocks r r` to `BlockShape.uniform 2 r`
(`twoBlocks_rankCast_eq_uniform`), and the two factor families agree up to that
cast (`twoBlockFactors_heq`). So `productFunctor_obj_eq_of_heq` and
`rankCast_isIrreducible_iff` from `JuxtaposedSwapFromLibrary` move the
irreducibility to the uniform shape.
