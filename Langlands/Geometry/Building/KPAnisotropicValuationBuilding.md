# The valuation-building quotient for an anisotropic group

Let `F` be a nonarchimedean local field, with the existing `ValuativeRel F`,
`TopologicalSpace F` and `IsNonarchimedeanLocalField F` instances. Let `G` be a
connected reductive `F`-group with `IsAnisotropic G` (the split rank of `G` itself
is zero). The `IsAffineHom G.X.hom` instance used by `ValuationBuildingData`
follows from connected reductivity. The construction is independent of
characteristic and needs no splitting extension, torus choice or integral
model.

## The split torus and its centralizer

Use `TorusExistence.trivialTorusHom G`, the closed identity section from the
trivial split torus. Its maximality is the imported algebraic theorem
`TorusExistence.isMaximalSplitTorus_trivialTorusHom G ha` from
[the anisotropic maximal split torus module](../../GroupScheme/Torus/AnisotropicTrivialMaximalSplit.md).
That theorem needs `IsSeparated G.X.hom`, which follows from the affine
structure morphism. This module does not prove maximality again.

`CentralizerDatum.ofAnisotropicGroup` works at any prescribed maximal split
torus `i` of such a group in the local-field interface. It uses the published
all-test centralizer equality `IsAnisotropic.torusCentralizer_eq_top` to take
`Z = G`, with `j = 𝟙 G` and `s = i`. The Library's real comparison for the
represented centralizer of a maximal split torus gives the required
bijectivity of restriction evaluation. No new algebraic comparison is
assumed or proved here.

## The apartment and reduced quotient

`ValuationBuildingData.ofAnisotropicGroup` applies the published
`ofIsAnisotropic` constructor to that explicit split torus and centralizer.
It uses the normalized empty valuation, represented by
`RootFunctionFamily.constantTop`, so the standard apartment is its singleton
translation orbit. `ofAnisotropicGroup_relativeRoots` and
`ofAnisotropicGroup_affineRoots` prove that the actual relative and ordinary
affine root sets are empty. The latter uses the fact that each affine root
has a derivative indexed by an actual relative root.
`ofAnisotropicGroup_apartmentPoint` is the element of the singleton given by
the normalized empty family.

The published `KPApartmentData.satisfiesApartmentAxioms_of_relativeRoots_eq_empty`
applies to this apartment using `ofAnisotropicGroup_relativeRoots`. It gives
full centralizer V 6, V 7 and AS 2–AS 5 with the Library's derivative-spanning
rank-zero convention.

`ofAnisotropicGroup_uniqueReducedBuilding` gives `Unique` on the original
`ReducedBuilding` quotient, not on a replacement one-point type. Its
specified point is the image of `ofAnisotropicGroup_apartmentPoint`. The
published root-free quotient argument gives subsingletonness: the apartment
is a singleton, every rational point normalizes the split subtorus, and the
normalizer fixes the image of the single apartment point. Every reduced
quotient point is a rational-point translate of that image. The group action
is the one on the existing quotient throughout.

## Source and scope

This is a derived construction using the Library's
[empty-root apartment](RootFreeApartmentConstruction.md) and
[root-free quotient geometry](RootFreeBuildingGeometry.md). In
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Definition 6.1.2,
Lemma 6.1.6, Definition 6.1.7 and §6.1.8 (printed pp. 199–201 / PDF
pp. 230–232) give the root-indexed valuations, their translations and the
normalizer action. Definition 6.3.4 (printed p. 218 / PDF p. 249) defines the
ordinary affine roots, and Remark 7.6.5, equation (7.6.2) (printed p. 266 /
PDF p. 297), gives the reduced quotient presentation. The authors' corrections
of 1 November 2024 leave these definitions and (7.6.2) in place (PDF pp. 32–36).
In particular the added AS 5 premise at the start of Chapter 7 is not assumed
here: the single-apartment AS 5 assertions are verified in rank zero by the
imported root-free theorem.

Proposition 9.3.9 (printed p. 335 / PDF p. 366; unchanged in the Chapter 9
corrections, PDF pp. 39–41) also has a one-point conclusion, but for the
**descended** reduced building under anisotropy of `G_der`, with an additional
unique Γ-chamber assertion. Neither the comparison to that descended building
nor the assertion about the Γ-chamber is part of this module. The enlarged
building, parahoric models, their integral points, and the full building
axioms and descent certificate remain separate.

Registered sources: `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, and
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
