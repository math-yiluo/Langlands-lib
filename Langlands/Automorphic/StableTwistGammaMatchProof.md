# Stable pair gamma comparison under highly ramified twists: proof

The theorem
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.stableTwistPairGammaMatchStatement.{u, uV, uE}`
proves the unchanged Library proposition
`Langlands.ClassFieldTheory.Global.RelativeWeilGroup.StableTwistPairGammaMatchStatement`
(module `Langlands.Automorphic.StableTwistGammaMatchStatement`) at three independent universe
levels. It adds no hypothesis and introduces no definition. The proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

In words: let `K` be a p-adic field, `ε` a common-closure local-constant system for `eC`, `e`
a rank-one candidate with `IsBaseReciprocity K e eC`, and `ψ` a nontrivial additive character.
Let `π`, `π'` be classes of ranks `r + 1`, `t + 1` with `ψ`-generic representatives, on which
the scalar matrices act by `ω`, `ω'`. Let `X`, `Y` be pair classes with continuous
representatives of ranks `r + 1`, `t + 1`, determinants `ω ∘ e`, `ω' ∘ e` and arbitrary
monodromy. Then there is a bound `A` such that, for every quasi-character `χ` of conductor at
least `A` and every twist `πχ` of `π` by `χ`, the pair gamma match
`IsPairGammaMatch K eC ε hε ψ πχ π' (twistClass (weilCharacter K e χ) X) Y` holds.

## Implemented proof

The proof is one term. It applies the conditional assembly
`Automorphic.StableTwist.stableTwistPairGammaMatch_of` (module
`Langlands.Automorphic.StableTwist.Assembly`; its Markdown gives the argument) to proofs of its
three hypotheses:

1. `RankinSelberg.pairGammaTwistExchange.{u, u, u}` (module
   `Langlands.Representation.RankinSelberg.PairGammaTwistExchangeProof`) proves
   `PairGammaTwistExchangeStatement`: a twist by `χ ∘ det` moves between the two factors of
   a symmetric JPSS gamma certificate.
2. `ArithmeticStableTwist.arithmeticStableTwistGamma.{u, uV, uE}` (module
   `Langlands.Automorphic.StableTwist.ArithmeticDeepTwist`) proves
   `ArithmeticStableTwistGammaStatement`. After a twist of large conductor, the arithmetic
   pair gamma factors of Weil–Deligne pairs with the same ranks and determinants agree.
3. `principalSeriesPairGammaMatchStatement.{u, uV, uE}` (Library module
   `Langlands.Automorphic.PrincipalSeriesGammaMatchProof`) proves
   `PrincipalSeriesPairGammaMatchStatement`: the pair gamma match for generic constituents
   of principal series and the matching diagonal Weil–Deligne pairs.

## Supporting modules of this proof

- `Langlands.Representation.RankinSelberg.PairGammaTwistExchangeIntegrals` and
  `PairGammaTwistExchangeProof`: proof of the twist exchange (item 1).
- `Langlands.Automorphic.StableTwist.ArithmeticDeepTwist`: proof of arithmetic stability
  (item 2).
- `Langlands.Representation.RankinSelberg.StableTwist.JPSSStability`: two-factor
  Jacquet–Shalika stability of JPSS pair gamma factors for any additive character.
- `Langlands.Automorphic.StableTwist.ClassStability`: the same stability for class gamma
  factors of generic classes.
- `Langlands.Automorphic.StableTwist.Assembly`: the conditional assembly.

Each module's paired Markdown describes its implemented proof.

## Sources

The overall argument is Henniart, *On the local Langlands conjecture for GL(n): the cyclic
case*, Ann. of Math. 123 (1986), Lemma 4.2 and its proof, printed p. 158, and §4.3. It
compares both sides with principal series attached to characters with the same product. On
the representation side it uses Jacquet–Shalika stability (Jacquet and Shalika, Math. Ann.
271 (1985), Proposition (4.1)). On the arithmetic side it uses Deligne–Henniart stability
(Deligne and Henniart, Invent. Math. 64 (1981), Théorème 4.6).
