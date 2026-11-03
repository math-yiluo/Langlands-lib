# Orbit maps of affine group schemes on affine schemes, in coordinates

Worker 281.

Internal support for the proof of the Kostant–Rosenlicht theorem
(`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement`; Milne,
*Algebraic Groups* (2017), Theorem 17.64). This module translates the orbit
map of a rational point into an algebra map between coordinate algebras, and
shows that it intertwines right translations on the group with translations on
the acted-on scheme. It works over an arbitrary commutative ring `R`.

The setting: `U : GroupScheme (Spec R)` with an identification
`j : (algSpec R).obj (op B) ≅ U.X` of its underlying scheme with the spectrum
of an `R`-algebra `B`, an action `a : SchemeAction U X` on `X : Over (Spec R)`,
an identification `jX : (algSpec R).obj (op A) ≅ X`, and a section
`x : 𝟙_ (Over (Spec R)) ⟶ X`. The corepresentation of the points of `U` by `B`
is the published `AffineLinearEmbedding.corepresentableBy U j`.

All definitions here are derived internal constructions, not taken from the
literature: they write the standard equivariance of orbit maps in the given
coordinates.

## Definitions

- `toBase C`: the structure morphism `Spec C → Spec R`, written as the image
  under `algSpec R` of `Algebra.ofId R C`.
- `invOrbit a x : U.X ⟶ X`: the inverted orbit map `u ↦ u⁻¹ • x`, i.e.
  `a.act (𝟙 U.X)⁻¹ (toUnit U.X ≫ x)`.
- `coordMap j a jX x : A ⟶ B`: the comorphism of
  `j.hom ≫ invOrbit a x ≫ jX.inv`, obtained by full faithfulness of `algSpec`.
- `leftTranslate a jX g : A ⟶ A`, for a point `g : Spec R ⟶ U.X`: the
  comorphism of `a.act (toBase A ≫ g⁻¹) jX.hom ≫ jX.inv`, i.e. of the
  translation `y ↦ g⁻¹ • y` of `X`, transported to `Spec A`.
- `basePoint j v : Spec R ⟶ U.X`: the point of `U` classified by an algebra
  map `v : B →ₐ[R] R`, i.e. `(algSpec R).map (ofHom v).op ≫ j.hom`.

## Results

- `comp_toBase`: every morphism `w : Spec D ⟶ Spec C` satisfies
  `w ≫ toBase C = toBase D`. Proof: `w` is the image of an algebra map, and
  algebra maps out of `R` are unique.
- `comp_invOrbit`: for `w : T ⟶ U.X`,
  `w ≫ invOrbit a x = a.act w⁻¹ (toUnit T ≫ x)`, by naturality of the action
  and `GrpObj.comp_inv`.
- `orbit_eq_inv_comp_invOrbit`: the orbit map
  `a.act (𝟙 U.X) (toUnit U.X ≫ x)` equals `(𝟙 U.X)⁻¹ ≫ invOrbit a x`
  (`comp_invOrbit` and `inv_inv`).
- `algSpec_map_coordMap`, `algSpec_map_leftTranslate`: the defining equations
  of the two comorphisms.
- `algSpec_map_rightTranslate_comp`: the morphism of spectra induced by
  `productMap id (ofId ∘ v) ∘ comul (corepresentableBy U j)`, followed by
  `j.hom`, is `j.hom * (toBase B ≫ basePoint j v)`; that is, it is right
  multiplication by the point classified by `v`. Proof: the published
  `pt_productMap_comp_comul`. The algebra map here is, by definition, the
  right translation `charTranslate (corepresentableBy U j) v` of
  `KostantRosenlicht.Hopf` when `R = CommRingCat.of k` for a field `k`.
- `coordMap_comp_rightTranslate`: in `CommAlgCat`,
  `coordMap ≫ ofHom (productMap id (ofId ∘ v) ∘ comul _) =
  leftTranslate a jX (basePoint j v) ≫ coordMap`. As algebra maps: the
  right translate by `v` of `coordMap c` is `coordMap` of the left translate
  of `c`. Geometrically this is `(u g)⁻¹ • x = g⁻¹ • (u⁻¹ • x)`. Proof: apply
  `algSpec`, which is faithful, cancel the isomorphism `jX`, and rewrite with
  `SchemeAction.naturality`, `comp_toBase`, `algSpec_map_rightTranslate_comp`,
  `comp_invOrbit`, `SchemeAction.act_mul` and `mul_inv_rev`.
- `isClosed_range_orbit`: if the range of
  `PrimeSpectrum.comap (coordMap j a jX x)` is closed, then so is the range of
  the underlying map of the orbit map. Proof: by `orbit_eq_inv_comp_invOrbit`
  the orbit map is `((𝟙 U.X)⁻¹ ≫ j.inv) ≫ (algSpec R).map (coordMap ..).op ≫
  jX.hom`. Inversion is an involution, so the first factor is an isomorphism,
  as is `jX.hom`. Their underlying maps are homeomorphisms, and the middle
  factor's underlying map is `PrimeSpectrum.comap` of `coordMap`. The range of
  the composite is therefore the image of the closed set under the
  homeomorphism of `jX.hom`.

The inversion is used so that the orbit map intertwines right translations on
`U`, which is the form of translation stability that
`KostantRosenlicht.range_comap_eq_zeroLocus` (module
`KostantRosenlicht.Surjective`) assumes.
