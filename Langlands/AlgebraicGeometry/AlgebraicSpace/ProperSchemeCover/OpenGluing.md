# Gluing sections of an fppf sheaf along an open cover

Helper module for the proof of `ProperSchemeCoverStatement`.

## Declarations

- `openOver T U`, `openOverι T U`, `openOverHomOfLE T h`: an open subscheme `U` of a scheme `T`
  over `S`, viewed as a scheme over `S`; its inclusion into `T`; and the inclusion `U ⟶ V` for
  `U ≤ V`. `openOverHomOfLE_ι` records that the inclusions are compatible.
- `openOver_covering`: an open cover `U : ι → T.Opens` (`IsOpenCover U`) gives a covering sieve
  of `T` in the fppf topology on schemes over `S`.
- `exists_inf_lift`: two morphisms `g : Z ⟶ U` and `h : Z ⟶ V` with the same composite to `T`
  factor through `U ⊓ V`.
- `exists_glue`: for an fppf sheaf `F`, sections `x i ∈ F(U i)` whose restrictions to
  `U i ⊓ U j` agree glue to a section `y ∈ F(T)` restricting to each `x i`.
- `openOver_covering_le`, `exists_glue_le`: the same two statements for opens `U i ≤ V` with
  `⨆ i, U i = V`, covering the open subscheme `V` of `T` instead of `T` itself.

## Proof

The covering statement reduces, via `Sieve.overEquiv_ofArrows`, to Mathlib's statement that the
open cover `T.openCoverOfIsOpenCover U hU` generates a covering sieve in the Zariski topology,
which is coarser than the fppf topology (`Scheme.zariskiPrecoverage_le_fppfPrecoverage`).
The lifting lemma uses `IsOpenImmersion.lift` for the open immersion of `U ⊓ V`. Gluing uses the
sheaf condition for the presieve of arrows (`Presieve.isSheafFor_arrows_iff`): its compatibility
condition for `g, h` with equal composites to `T` follows by factoring `g, h` through
`U ⊓ V` and using the assumed agreement on the intersection.

For the relative version, the inclusions `U i ⟶ V` (`Scheme.homOfLE`) are open immersions that
jointly cover `V`, so `Scheme.Cover.mkOfCovers` makes them a Zariski cover of `V`. In the
compatibility condition, two morphisms with equal composites to `V` also have equal composites
to `T`, so they factor through `U i ⊓ U j` by `exists_inf_lift`.
