# Jacquet modules of contragredients for dynamic parabolics, with Haar reciprocity

Module `Langlands.Representation.Exponents.LeviJacquetContragredientReciprocity`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Content

The setting is that of `nonempty_leviJacquetContragredient_iso_of_dynamic` in
`Langlands.Representation.Exponents.LeviJacquetContragredientDynamic`. There is a Hausdorff
nonarchimedean local field `k` and a group scheme `G` over `k` with affine structure map.
Its rational points `G(k)` carry the Library point topology and are assumed locally compact
and nonarchimedean. `P = MN` and `P̄ = MN̄` are represented parabolics with Levi
decompositions and a common Levi embedding, `mbar ≫ pbar = m ≫ p`. For a cocharacter `χ`
the point images of `N`, `M` and `N̄` in `G(k)` are `N(χ)`, `M(χ)` and `N(χ⁻¹)`.

- `nonempty_leviJacquetContragredient_iso_of_dynamic_of_leviAdjoint`: assume the Library
  statements `UniformCompressionStabilizationStatement` (Renard VI.9.1, uniform
  stabilization of compression) and `Dynamic.LeviAdjointDeterminantReciprocityStatement`,
  and that `G` is connected reductive. Then there is a natural isomorphism
  `r_{P̄}^G(π~) ≅ (r_P^G π)~` of functors from smooth complex representations of `G(k)`
  to smooth representations of `M(k)`. This is the conclusion of
  `LeviJacquetContragredientStatement` for this pair of parabolics.
- `nonempty_leviJacquetContragredient_iso_of_dynamic_of_reflection_centralSplitTorus`: the
  same conclusion with `Dynamic.LeviAdjointDeterminantReciprocityStatement` replaced by
  `RelativeRootReflectionExistenceStatement` and `CentralSplitTorusCharacterStatement`.

These results are conditional on the named Library statements. None of them is proved in
the Library at the time of writing.

## Provenance

Renard 2026, VI.9.6, second Theorem (VI.9.6.2) (printed p.201, PDF p.207), for the
represented parabolics of a cocharacter. The module only combines two earlier results and
adds no mathematics.

## Proof

Each theorem applies `nonempty_leviJacquetContragredient_iso_of_dynamic`. Its premise
`hrec`, reciprocity of the Haar scaling characters of `N(χ⁻¹)(k)` and `N(χ)(k)` on
`M(χ)(k)`, is supplied by `dynamicOppositeHaarReciprocity_of_leviAdjoint` (respectively
`dynamicOppositeHaarReciprocity_of_reflection_centralSplitTorus`). These take the abstract
subgroups `pointImage (nbar ≫ pbar)`, `pointImage (m ≫ p)` and `pointImage (n ≫ p)`
together with the equalities `hNbar`, `hM` and `hN`.
