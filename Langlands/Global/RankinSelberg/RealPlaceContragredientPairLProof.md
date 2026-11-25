# Proof: real-place pair factors of contragredient realizations

Module `Langlands.Global.RankinSelberg.RealPlaceContragredientPairLProof`. The theorem

```lean
theorem Langlands.Global.RankinSelbergGlobal.realPlaceContragredientPairL :
    RealPlaceContragredientPairLStatement.{u}
```

proves `Langlands.Global.RankinSelbergGlobal.RealPlaceContragredientPairLStatement` (module
`RealLocalTheoryReduction`) at an arbitrary universe `u`. Unfolded, the statement is

```lean
∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (ds es dds ees : List RealBlock),
    T.realization.HasRealPlaceParameter v ds →
    T'.realization.HasRealPlaceParameter v es →
    Td.realization.HasRealPlaceParameter v dds →
    Td'.realization.HasRealPlaceParameter v ees →
    (realPairLFactor dds ees).denominator =
      (realPairLFactor (ds.map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock)).denominator
```

In words: let `T`, `Td` be actual cuspidal realizations of `GL_(r+1)` over a number field with
compact adele quotient, `Td` contragredient to `T`, and `T'`, `Td'` actual cuspidal realizations
of `GL_(t+1)`, `Td'` contragredient to `T'`. If `ds`, `es`, `dds`, `ees` are parameters of `T`,
`T'`, `Td`, `Td'` at the same real place `v`, then the pair `L`-factor of `dds` and `ees` equals
that of the dualized blocks `ds.map dualBlock` and `es.map dualBlock` (`dualBlock` replaces the
inducing character of a block by its inverse); as a reciprocal-entire factor this is equality of
the denominators.

## Proof as implemented

The proof is a single term of five Library theorems.

1. `realPlaceContragredientPairLReduction` (module `RealPlaceContragredientReduction`) proves
   `RealPlaceContragredientPairLReductionStatement.{u}`, the implication
   `Automorphic.CuspidalArchimedeanStandardIrreducibleStatement.{u} →
   RealStandardPairingPairLStatement → RealPlaceContragredientPairLStatement.{u}`. From the
   contragredient pairing of `T` and `Td` it builds a nonzero invariant pairing of the standard
   modules of `ds` and `dds` at `v`, and likewise for `es` and `ees`; the local pairing statement
   then replaces `dds` by `ds.map dualBlock` and `ees` by `es.map dualBlock`.
2. `Langlands.Automorphic.cuspidalArchimedeanStandardIrreducible` (module
   `Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof`) proves
   `CuspidalArchimedeanStandardIrreducibleStatement.{u}`: the standard module of a parameter of a
   cuspidal realization at an archimedean place is irreducible.
3. `RealStandardPairingPairLStatement` (two irreducible real standard modules with a nonzero
   invariant pairing have the same pair `L`-factors against every list of blocks, after dualizing
   the first) is the term
   `realStandardPairingPairLReduction realStandardDualPairing realStandardIntertwinerPairL`:
   - `realStandardPairingPairLReduction` (module `RealStandardPairingReduction`) proves
     `RealStandardPairingPairLReductionStatement`, the implication
     `RealStandardDualPairingStatement → RealStandardIntertwinerPairLStatement →
     RealStandardPairingPairLStatement`;
   - `realStandardDualPairing` (module `RealStandardDualPairingProof`) proves
     `RealStandardDualPairingStatement`: an irreducible real standard module `I(ds)` has an
     invariant pairing with the standard module of `ds.map dualBlock`, nondegenerate on the
     second side;
   - `realStandardIntertwinerPairL` (module `RealStandardIntertwinerPairLProof`) proves
     `RealStandardIntertwinerPairLStatement`: two irreducible real standard modules related by a
     nonzero intertwiner have the same pair `L`-factors against every list of blocks.

## Declarations

- `realPlaceContragredientPairL : RealPlaceContragredientPairLStatement.{u}` (theorem).

## Provenance

The statement is an internal formulation of the Library (one of the four premises of
`RealPlaceLocalTheoryReductionStatement`, module `RealLocalTheoryReduction`); its page cites no
source of its own. The fact it records is that the contragredient of an irreducible admissible
representation of `GL_n(ℝ)` has the dual Langlands parameter, so that the pair `L`-factors of
the contragredients are those of the dual parameters. In A. W. Knapp, *Local Langlands
correspondence: the archimedean case*, in U. Jannsen, S. Kleiman and J.-P. Serre (eds.),
*Motives*, Proc. Sympos. Pure Math. 55, Part 2 (1994), 393–410 (registered as
`knapp-1994-archimedean-llc`; in the volume PDF page = printed page + 10): the building blocks
(2.2a)–(2.2b) and the induced representations (2.4), and Theorem 1 (Langlands classification,
(c): `J(σ_1, …, σ_r)` and `J(σ'_1, …, σ'_r')` are infinitesimally equivalent if and only if
`r' = r` and the `σ'_i` are a permutation of the `σ_i`), printed p. 400 (PDF page 410); Theorem 2
(the local Langlands correspondence for `GL_n(ℝ)`), printed p. 403 (PDF page 413).
