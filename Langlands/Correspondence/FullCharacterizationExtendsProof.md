# Henniart's extension from full pair factors at one character

`Langlands.Correspondence.fullCharacterizationExtends` proves the published
proposition `Langlands.Correspondence.FullCharacterizationExtendsStatement.{uF, uP, uA} F`
for every prime `p`, every `F : PadicField.{uF} p` and independent parameter
and automorphic carrier universes `uP` and `uA`. This is Henniart, *Une
caractérisation de la correspondance de Langlands locale pour GL(n)*, Bull. SMF
130 (2002), Corollary 1.6 (printed p. 591; proof in Section 3.4).

For a supercuspidal map `c0`, a full map `τ`, a nontrivial additive character
`ψ` and a reciprocity candidate `e`, the hypotheses are exactly those of the
statement: `IsSupercuspidalCorrespondence F c0`, `IsGeometricReciprocity F e`,
`RankOneCompatibility F e τ` and `FullFactorCompatibilityAt F e ψ τ`. The
conclusion is `ExtendsSupercuspidal F c0 τ`: `τ` sends the zero-monodromy class
of every irreducible Weil class `σ` to the supercuspidal class `c0 σ`.

## The implemented proof

The theorem applies the published conditional reduction
`fullCharacterizationExtends_of_inputs` (module
`Langlands.Correspondence.FullCharacterizationExtendsReduction`) to published
proofs of its three inputs:

- H1, the supercuspidal local converse theorem
  `RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uA, uA}`:
  `RankinSelberg.supercuspidalLocalConverse`
  (`Langlands.Representation.RankinSelberg.SupercuspidalLocalConverseProof`).
- H2, Henniart 2002, Theorem 1.6(b),
  `RankinSelberg.SupercuspidalLFactorCharacterizationStatement.{uF, uA, uA}`:
  `RankinSelberg.supercuspidalLFactorCharacterization`
  (`Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationProof`).
- H4, uniqueness of local-constant systems for every reciprocity family
  `eC` of `F`: `fun eC => LocalFactor.NonabelianSystem.unique F eC`
  (`Langlands.LocalFactor.NonabelianUniquenessProof`), at universes
  `.{uF, uP}`.

The mathematical argument is the one carried out in the reduction module. It
proves `τ D = c0 σ` for the zero-monodromy class `D` of every irreducible Weil
class `σ` by strong induction on the rank:

1. Uniqueness of the normalized reciprocity family and H4 identify the
   local-constant system of `τ`'s epsilon compatibility with that of the
   supercuspidal correspondence `c0`; the two reciprocity candidates have the
   same Weil characters.
2. Rank one follows from rank-one compatibility of `c0` and `τ`.
3. In rank at least two, the induction hypothesis and surjectivity of `c0`
   show that every supercuspidal class of smaller rank is `τ D'` for the
   zero-monodromy class `D'` of some irreducible Weil class `σ'`.
4. Supercuspidality: L-compatibility of `τ` and the lower-rank parameter
   criterion (the pair L-factor of irreducible Weil classes of different ranks
   is `1`) show that the Langlands pair L-polynomial of `τ D` against every
   supercuspidal of smaller rank is `1`; H2 (direction (ii) ⇒ (i)) makes
   `τ D` supercuspidal.
5. Equality: epsilon compatibility of `τ` and of `c0` with the same system
   gives equal pair epsilon factors of `τ D` and `c0 σ` against every
   supercuspidal of smaller rank; for supercuspidal pairs these are the
   symmetric JPSS factors, and H1 gives `τ D = c0 σ`.

The hypothesis `IsGeometricReciprocity F e` is not used by the reduction.
Supercuspidality of the images and their equality with `c0` are derived from
the stated hypotheses, not assumed. The axioms of the theorem are `propext`,
`Classical.choice` and `Quot.sound`.
