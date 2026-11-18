# A surjective étale morphism from an affine scheme onto a quasi-compact scheme

Lean module: `Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover`.

## Definitions

Let `Y : Scheme.{u}` be quasi-compact (`[CompactSpace Y]`), and let
`𝒰 := Y.affineCover.finiteSubcover` be the finite affine open cover that Mathlib extracts from
the affine cover of `Y` by compactness.

- `Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover.coverRing Y : CommRingCat.{u}` is
  the ring of global sections `Γ(∐ 𝒰.X, ⊤)` of the disjoint union of the finitely many affine
  schemes `𝒰.X i`.
- `Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover.specCover Y :
  Spec (coverRing Y) ⟶ Y` is `(∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f`. The coproduct is affine,
  so it is isomorphic to `Spec (coverRing Y)`. The morphism goes back to the coproduct along
  the inverse of that isomorphism and then maps each summand `𝒰.X i` to `Y` by its open
  immersion `𝒰.f i`.

`specCover_properties Y` states that `specCover Y` is surjective, flat, geometrically reduced,
locally of finite type, étale and smooth.

## Statement

`Langlands.AlgebraicGeometry.QuasiCompactAffineEtaleCover.exists_spec_cover` takes a scheme
`Y : Scheme.{u}` whose underlying space is compact (`[CompactSpace Y]`, i.e. `Y` is
quasi-compact). It asserts that there are a commutative ring `R : CommRingCat.{u}` and a morphism
`p : Spec R ⟶ Y` such that `p` is

1. surjective (`Surjective p`),
2. flat (`Flat p`),
3. geometrically reduced (`GeometricallyReduced p`),
4. locally of finite type (`LocallyOfFiniteType p`),
5. étale (`Etale p`),
6. smooth (`Smooth p`).

## Provenance and purpose

This is an internal helper for Task 7618, the proof of
`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionStatement`. Worker 7, who writes the
scheme-level assembly, asked for it: a quasi-compact scheme is covered by the spectrum of one
ring through a morphism that is surjective, flat, locally of finite type and geometrically
reduced. Geometric questions about `Y` can then be moved to an affine scheme. The construction is
the standard one: the disjoint union of a finite affine open cover is affine. Mathlib uses the
same morphism to prove `AlgebraicGeometry.compactSpace_iff_exists`, but only records that it is
surjective.

## Proof

`exists_spec_cover Y` takes `R := coverRing Y` and `p := specCover Y` and uses
`specCover_properties Y`. That theorem is proved as follows.

1. Let `𝒰 := Y.affineCover.finiteSubcover`. This finite subcover of the affine open cover exists
   because `Y` is compact. Then `p := specCover Y = (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f`. The
   coproduct of finitely many affine schemes is affine, so `∐ 𝒰.X ≅ Spec Γ(∐ 𝒰.X, ⊤)`.
2. `p` is surjective by the Mathlib instance for the descended map of an open cover, as in
   Mathlib's proof of `compactSpace_iff_exists`.
3. Each `𝒰.f i` is an open immersion, hence étale. Étaleness is local on the source, so
   `IsZariskiLocalAtSource.sigmaDesc` makes `Sigma.desc 𝒰.f` étale. Composing with the
   isomorphism `isoSpec.inv` keeps it étale (Mathlib instances).
4. Étale morphisms are smooth, flat and locally of finite type (Mathlib instances).
5. A smooth morphism is geometrically reduced by the published Library lemma
   `Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth`.

The module sets `backward.isDefEq.respectTransparency false` (and its `.types` variant), as other
Library modules that use `IsZariskiLocalAtSource.sigmaDesc` do. Without it the instance
`IsZariskiLocalAtSource @Etale`, derived from `HasRingHomProperty`, is not found.
