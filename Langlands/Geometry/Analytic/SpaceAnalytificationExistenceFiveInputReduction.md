# Conditional existence of analytifications from five inputs

This module is a conditional assembly with derived provenance. The published seven-input
reduction `SpaceAnalytificationExistenceReductionStatement` has two inputs that are now
proved, and this module removes both:

- input 4, `AffineAnalytificationFibreProductStatement.{u,u,u,u}`, is supplied by the
  published theorem `Langlands.Analytic.AffineAnalytification.affineAnalytificationFibreProduct`
  (module `AffineAnalytificationFibreProductProof`), specialized to `.{u,u,u,u}`;
- input 7, joint surjectivity, is supplied by `exists_mem_range_localizedHom` from
  `AffineAnalytificationJointSurjectivity`.

**The target statement `SpaceAnalytificationExistenceStatement` is not proved.** The
reduction still has five formal premises. At the Library commit this module was built on
(`f050c0b1b525624bc32c1e7c25a8d2841bb2d4e0`), none of the five has a Library proof.

## Declarations

- `SpaceAnalytificationExistenceFiveInputReductionStatement` (the entry declaration) is a
  proposition. It says that five premises imply `SpaceAnalytificationExistenceStatement.{u}`.
  The premises are inputs 1, 2, 3, 5 and 6 of `SpaceAnalytificationExistenceReductionStatement`,
  word for word and in the same order:
  1. analytic quotients of étale affine chart families of separated algebraic spaces. This
     is the chart form of Conrad–Temkin (2009), Theorem 4.2.2, proposed as
     `SpaceAnalytificationChartQuotientStatement`;
  2. morphisms to an analytic space form a sheaf on the small étale site (Berkovich 1993,
     §4.1; Conrad–Temkin 2009, Theorem 4.1.2). This is proposed as `EtaleHomSheafStatement`;
  3. étaleness of a morphism descends through a jointly surjective family of étale maps to
     its source. This is proposed as `LocalizedEtaleSourceDescentStatement`;
  4. the analytification of an étale map of finitely presented `K`-algebras is étale in the
     localized category (Berkovich 1990, Proposition 3.4.6(3)). This is proposed as
     `AffineAnalytificationLocalizedEtaleStatement`. It is input 5 of the seven-input
     reduction;
  5. the Library statement `LocalizedEtalePullbackStatement.{u,u} K` for every `K`. It is
     input 6 of the seven-input reduction. The Library proves it conditionally:
     `localizedEtalePullback_of_targetLocality_and_finitePieces` derives it from
     `FiniteOverTargetLocalityStatement` and the proved `FinitePiecesEtaleAllPiecesStatement`.
     In turn, `finiteOverTargetLocality_of_descent` derives
     `FiniteOverTargetLocalityStatement` from `FiniteAffinoidAlgebraDescentStatement`.

  Premises 1–4 are not Library statements, so they are written out in full.
- `spaceAnalytificationExistenceFiveInputReduction` proves
  `SpaceAnalytificationExistenceFiveInputReductionStatement.{u}`. It applies the published
  theorem `spaceAnalytificationExistenceReduction` to the five premises. Input 4 is
  `affineAnalytificationFibreProduct.{u,u,u,u}`. Input 7 is `exists_mem_range_localizedHom`,
  with the family index in `Type u`.

## Scope

All objects live in the Library's localized category `LocalizedCategory.{u,u,u}` over a field
`K : Type u`. The only new mathematics behind this module is the proof of input 7.
