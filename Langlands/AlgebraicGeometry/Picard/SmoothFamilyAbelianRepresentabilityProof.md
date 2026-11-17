# Proof: the shared abelian-scheme representer for smooth-family Picard classes

This module proves
`Langlands.AbelianScheme.SmoothFamilyAbelianRepresentabilityStatement.{u}` as the theorem
`Langlands.AbelianScheme.smoothFamilyAbelianRepresentability`.

The proof is a single application of two published results:

- the general-base reduction
  `Langlands.AbelianScheme.smoothFamilyAbelianRepresentabilityOfFiniteType`
  (module `Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof`),
  whose type is `SmoothFamilyAbelianRepresentabilityOfFiniteTypeStatement.{u}`, that is
  `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u} →
  SmoothFamilyAbelianRepresentabilityStatement.{u}`;
- the finite-type case
  `Langlands.AbelianScheme.finiteTypeSmoothFamilyAbelianRepresentability :
  FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`
  (module `Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof`).

For orientation: the reduction glues representers over an affine open cover of the
quasi-separated base (`smoothFamilyAbelianRepresentabilityOfOpenCover`), spreads each affine
piece to a finitely generated subring (`affineObjectSpreading`), applies the finite-type case
there, base-changes the universal pair (`smoothFamilyUniversalBaseChange`) and transports it
along the spreading isomorphism (`smoothFamilyUniversalIsoTransport`). The finite-type case is
obtained from the representability of the fppf Picard class sheaf by a scheme
(`finiteTypeAbelianPicardSheafScheme`); its import closure does not use the general
`SmoothFamilyAbelianRepresentabilityStatement`, so the argument is not circular.

The constructed `B` is an actual abelian scheme over `S`, `L` is an actual rigidified
family on `B.X`, and the predicate `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` is
the unchanged Library predicate. No hypothesis is added.
