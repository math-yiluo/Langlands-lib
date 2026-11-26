# Twisted gluings over a base and their base change along closed immersions

Module `Langlands.AlgebraicGeometry.TwistedOpenGluingBaseChange`, namespace
`Langlands.AlgebraicGeometry.TwistedOpenGluing`. It continues
[`TwistedOpenGluing`](TwistedOpenGluing.md).

## Declarations

- `homOfLE_resLE`: restrictions `f.resLE` of a morphism to opens commute with the
  inclusions `homOfLE` of smaller opens.
- `Data.IsOver D π`: for `π : C ⟶ S`, every transition map `θ i j` is a morphism over
  `S`, i.e. `θ i j ≫ π = (V i ⊓ V j).ι ≫ π`.
- `Data.toBase hπ : D.glued ⟶ S`: the structure morphism, glued from `(V i).ι ≫ π`
  (`ι_toBase`). `smooth_toBase` and `locallyOfFiniteType_toBase`: if `π` is smooth
  (resp. locally of finite type), so is `toBase`; both properties are local on the source
  (Mathlib's `IsZariskiLocalAtSource.of_openCover` on the open cover of the glued scheme).

## Base change along a closed immersion

Fix `t : T ⟶ S` with `[IsClosedImmersion t]`.

- `VT t i = pullback.fst π t ⁻¹ᵁ V i` are the pulled-back pieces of `pullback π t`, and
  `ρ t i j` is the restriction of `pullback.fst π t` to the pulled-back overlap
  (`ρ_ι`).
- `θT hπ t i j = pullback.lift (ρ t i j ≫ θ i j) (ι ≫ pullback.snd π t)` are the
  pulled-back transition maps (`θT_fst`, `θT_snd`). They fix points because
  `pullback.fst π t`, a base change of the closed immersion `t`, is injective
  (`θT_pointwise`). `θT_self` and `θT_cocycle` follow from the corresponding properties of
  `D` by comparing both projections.
- `Data.baseChange hπ t : Data (pullback π t)` collects these.
- `κ hπ t i : VT t i ⟶ pullback (D.toBase hπ) t` is the base change of `ι i`
  (`κ_fst`, `κ_snd`). `isPullback_κ` shows that the square formed by `κ`, the
  restriction `r t i` of `pullback.fst π t` to `VT t i`, `ι i` and
  `pullback.fst (D.toBase hπ) t` is a pullback, by pasting the pullback squares of an open
  subscheme (`isPullback_morphismRestrict`) and of `pullback π t`, and Mathlib's
  `IsPullback.of_bot`. Hence `κ` is an open immersion with image the preimage of the image
  of `ι i` (`opensRange_κ`).
- `κ_compat`, `κ_pre`, `κ_cover` verify the hypotheses of `recognize` for the pulled-back
  data, using `glue` and `preimage_opensRange`.
- `baseChangeIso hπ t : (D.baseChange hπ t).glued ≅ pullback (D.toBase hπ) t`: gluing
  commutes with base change along a closed immersion, with
  `ι i ≫ (baseChangeIso hπ t).hom = κ hπ t i` (`ι_baseChangeIso_hom`).

## Provenance

Internal construction; the base change statement is the compatibility of the gluing of
local lifts with reduction used in Kai-Wen Lan, *Arithmetic compactifications of PEL-type
Shimura varieties*, Harvard thesis revised 14 March 2021, Proposition 2.1.2.2 (printed
p. 114, PDF p. 142) and Corollary 2.1.4.3 (printed pp. 122–123, PDF pp. 150–151), registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
