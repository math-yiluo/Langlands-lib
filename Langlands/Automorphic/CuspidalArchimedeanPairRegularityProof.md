# Proof: archimedean pair regularity of unitary cuspidal realizations

Module `Langlands.Automorphic.CuspidalArchimedeanPairRegularityProof`. The theorem

```lean
theorem Langlands.Automorphic.cuspidalArchimedeanPairRegularity :
    CuspidalArchimedeanPairRegularityStatement.{u}
```

proves `Langlands.Automorphic.CuspidalArchimedeanPairRegularityStatement` (module
`CuspidalArchimedeanComponentStatement`) at an arbitrary universe `u`. Unfolded, the statement is

```lean
∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T' →
    (∀ (v : {v : NumberField.InfinitePlace F // v.IsReal}) (ds ds' : List RealBlock),
      T.realization.HasRealPlaceParameter v ds →
      T'.realization.HasRealPlaceParameter v ds' →
        ∀ s : ℂ, 1 ≤ s.re → (realPairLFactor ds ds').denominator s ≠ 0) ∧
    ∀ (v : {v : NumberField.InfinitePlace F // v.IsComplex})
      (ds ds' : List ComplexCharacterData),
      T.realization.HasComplexPlaceParameter v ds →
      T'.realization.HasComplexPlaceParameter v ds' →
        ∀ s : ℂ, 1 ≤ s.re → (complexPairLFactor ds ds').denominator s ≠ 0
```

In words: let `T` and `T'` be actual cuspidal realizations of `GL_{r+1}` and `GL_{t+1}` over a
number field `F` (with compact adele quotient), both with unitary central characters. If `ds`
and `ds'` are standard-module parameters of `T` and `T'` at the same real place, the entire
denominator of `realPairLFactor ds ds'` does not vanish at any `s` with `1 ≤ Re(s)`; the same
holds at a complex place for `complexPairLFactor`.

## Proof as implemented

The proof is a single term: the Library reduction
`cuspidalArchimedeanPairRegularityReduction` (module
`CuspidalArchimedeanPairRegularityReductionProof`), which proves
`CuspidalArchimedeanPairRegularityReductionStatement.{u}`, applied in order to its six
premises, each a Library theorem:

1. `archimedeanStandardAdmissible` (module `ArchimedeanStandardAdmissibleProof`):
   `ArchimedeanStandardAdmissibleStatement`, every real and complex standard module is
   admissible.
2. `cuspidalArchimedeanStandardIrreducible` (module `CuspidalArchimedeanComponentIrreducibleProof`):
   `CuspidalArchimedeanStandardIrreducibleStatement.{u}`, the standard module of a parameter of
   a cuspidal realization at an archimedean place is irreducible.
3. `cuspidalArchimedeanStandardGeneric` (module `CuspidalArchimedeanStandardGenericProof`):
   `CuspidalArchimedeanStandardGenericStatement.{u}`, it is generic.
4. `cuspidalArchimedeanStandardUnitarizable` (module `CuspidalArchimedeanComponentUnitaryProof`):
   `CuspidalArchimedeanStandardUnitarizableStatement.{u}`, it is unitarizable when the central
   character is unitary.
5. `Archimedean.realUnitaryGenericPairRegularity.{0, 0}` (module
   `Langlands.Representation.Archimedean.RealUnitaryGenericPairRegularityProof`):
   `RealUnitaryGenericPairRegularityStatement.{0, 0}`, Getz–Hahn, Theorem 11.5.2, for
   `GL_n(ℝ)` with carriers in `Type`.
6. `Archimedean.complexUnitaryGenericPairRegularity.{0, 0}` (module
   `Langlands.Representation.Archimedean.ComplexUnitaryGenericPairRegularityProof`): the same
   for `GL_n(ℂ)`.

The reduction applies, at each place, the archimedean case of Theorem 11.5.2 to the standard
modules of the two parameters, which are irreducible, admissible, generic and unitarizable by
the first four premises. The reduction takes the real and complex cases at universes `0, 0`,
that is, for carriers in `Type`.

## Declarations

- `cuspidalArchimedeanPairRegularity : CuspidalArchimedeanPairRegularityStatement.{u}`
  (theorem).

## Provenance

J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations` (in Chapter 11, PDF page = printed page + 11).
Theorem 11.5.2, printed p. 305 (PDF page 316): for unitary `π`, `π'`, the local factor
`L(s, π × π')` is holomorphic and nonzero for `Re(s) ≥ 1`. On printed p. 309 (PDF page 320),
§11.7, after reducing to `π`, `π'` trivial on `A_{GL_n}`, `A_{GL_m}`: "`L(s, π_v × π'_v)`
converges absolutely for `Re(s) ≥ 1` for all `v` by Theorem 11.5.2." The theorem here is that
step at the archimedean places, for the Library's cuspidal realizations with unitary central
characters and their standard-module parameters, stated as nonvanishing of the entire
denominator of the reciprocal-entire pair factor.
