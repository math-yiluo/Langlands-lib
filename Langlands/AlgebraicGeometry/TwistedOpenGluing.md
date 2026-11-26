# Gluing open subschemes along transition maps that fix every point

Module `Langlands.AlgebraicGeometry.TwistedOpenGluing`, namespace
`Langlands.AlgebraicGeometry.TwistedOpenGluing`.

Infinitesimal deformations of a scheme are built by regluing its open pieces with
automorphisms that are the identity on underlying points. This module glues open
subschemes `V i` of one ambient scheme `C` along such transition maps. It specializes
the scheme gluing core `MkCore` of the Library's port of the Anthropic FLT formalization
(`P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.GlueData.MkCore`,
module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict`),
which in turn builds Mathlib's `Scheme.GlueData`.

## Definitions

- `IsPointwiseInclusion f`: a morphism `f : U ⟶ C` from an open subscheme `U` of `C`
  agrees with the inclusion `U.ι` on underlying points.
- `restrictTo f hf hWU hWQ`: for such `f` and opens `W ≤ U`, `W ≤ Q`, the restriction of
  `f` to `W`, as a morphism into the open subscheme `Q` (it exists because `f` fixes
  points). `restrictTo_ι` records `restrictTo f hf hWU hWQ ≫ Q.ι = C.homOfLE hWU ≫ f`.
- `Data C`: an index type `J`, opens `V : J → C.Opens` and transition maps
  `θ i j : (V i ⊓ V j) ⟶ C` such that
  - every `θ i j` is a pointwise inclusion (`pointwise`);
  - `θ i i` is the inclusion of `V i ⊓ V i` (`self`);
  - on `W = V i ⊓ V j ⊓ V k`, the restriction of `θ j k`, viewed in `V i ⊓ V j`, followed
    by `θ i j`, equals the restriction of `θ i k` (`cocycle`).

  The map `θ i j` sends the coordinates of the `j`-th piece on the overlap to those of
  the `i`-th piece.

## The glued scheme

- `O i j = (V i).ι ⁻¹ᵁ V j` is the overlap as an open of the `i`-th piece, `nest i j` its
  inclusion into `C` (range `V i ⊓ V j`, `range_nest`) and `toInf i j` its identification
  with the open `V i ⊓ V j`.
- `t i j : O i j ⟶ O j i` is the transition of the gluing core, obtained from `θ j i`.
  `t_nest` gives its composite into `C`, `t_nest_apply` shows it fixes points,
  `t_self` that `t i i = 𝟙`, and `t_inter` the inclusion of triple overlaps required by
  `MkCore`.
- `cocycle_core` derives the cocycle condition of `MkCore` from `cocycle` (for the indices
  `k, j, i`). The proof compares morphisms into `C` after cancelling open immersions, using
  `toTriple` (the triple overlap inside the `i`-th piece mapped onto
  `V k ⊓ V j ⊓ V i`) and `restrictRestrictComm_hom_ι_ι`.
- `core` is the gluing core, `glued` the glued scheme and `ι i : V i ⟶ glued` the open
  immersions.
- `glue i j`: `C.homOfLE (V i ⊓ V j ≤ V j) ≫ ι j = restrictTo (θ i j) … ≫ ι i`; a point of
  the overlap in the `j`-th piece is identified with its image under `θ i j` in the `i`-th
  piece. It is the gluing condition `MkCore.t_ι_ι` transported to the intersection.

## Morphisms out of the glued scheme and recognition

- `desc m hm`: morphisms `m i : V i ⟶ Y` with
  `C.homOfLE (V i ⊓ V j ≤ V j) ≫ m j = restrictTo (θ i j) … ≫ m i` glue to
  `glued ⟶ Y` (Mathlib's `Multicoequalizer.desc`; `core_compat` translates the condition
  to the nested overlaps). `ι_desc` and `hom_ext` are its universal property.
- `iSup_opensRange`: the images of the pieces cover the glued scheme.
  `preimage_opensRange`: `ι i ⁻¹ᵁ (ι j).opensRange = O i j` (the Library's
  `MkCore.preimage_opensRange`).
- `recognize κ hcov hpre hκ`: let `κ i : V i ⟶ Y` be open immersions whose images cover
  `Y` (`hcov`), with `(κ j) ⁻¹ᵁ (κ i).opensRange ≤ (V j).ι ⁻¹ᵁ V i` (`hpre`) and compatible
  with the transition maps in the sense of `desc` (`hκ`). Then `desc κ hκ` is an
  isomorphism `glued ≅ Y`. The inverse is glued on the open cover of `Y` by the images of
  the `κ i`; on an intersection of two images, `overlapLift` maps back into `V i ⊓ V j`,
  and `overlapLift_homOfLE`, `overlapLift_restrictTo` with `glue` give the compatibility.
  `ι_recognize_hom` records `ι i ≫ (recognize …).hom = κ i`.

## Provenance

The construction is internal. It is the gluing step in the construction of
infinitesimal lifts of smooth schemes from local lifts, as in Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis revised
14 March 2021, Lemma 2.1.1.7 and Proposition 2.1.2.2 (printed p. 114, PDF p. 142),
registered as `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. The scheme gluing
itself is Mathlib's, through the Library's port of the FLT gluing core.
