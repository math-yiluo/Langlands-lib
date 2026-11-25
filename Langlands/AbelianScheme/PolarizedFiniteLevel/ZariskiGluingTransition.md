# Transition maps of polarized isomorphisms onto pulled-back data

Helper module for Zariski gluing of ordinary polarized full-level data (used by `ModuliZariskiSheafOfRigidityProof`, which derives the Zariski sheaf property from rigidity).
A polarized isomorphism `θ : c ≅ c'.pullback b` over a base map `b : T ⟶ T'` induces
a scheme map from the abelian scheme of `c` to that of `c'`. When the data are rigid,
these maps are functorial in `b`.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`.

- `PolarizedIso.eq_of_rigid_source`: if every polarized automorphism of `c` is the
  identity, then any two polarized isomorphisms `c ≅ c'` are equal. This assumes
  rigidity of the source, whereas the separation module's `PolarizedIso.eq_of_rigid`
  assumes rigidity of the target.
- `PolarizedIso.overMap θ`: for `θ : PolarizedIso c (c'.pullback b)`, the map
  `hom θ.abelianIso.hom ≫ pullback.fst` from `c.abelian.X.left` to `c'.abelian.X.left`.
- `PolarizedIso.hom_snd`, `PolarizedIso.overMap_w`: `overMap θ` lies over `b`.
- `PolarizedIso.isPullback_overMap`: the square formed by `overMap θ`, the two structure
  maps and `b` is cartesian.
- `PolarizedIso.overMap_eq_id`: if `c` is rigid and `b = 𝟙`, then `overMap θ = 𝟙`.
- `PolarizedIso.overMap_comp`: if `c` is rigid and `b₁ ≫ b₂ = b₃`, then
  `θ₁.overMap ≫ θ₂.overMap = θ₃.overMap` for polarized isomorphisms over `b₁`, `b₂`
  and `b₃`.

## Proofs

`eq_of_rigid_source`: `θ.trans θ'.symm` is an automorphism of `c`, hence the identity, so
the abelian isomorphisms agree; the remaining fields are propositions.
`isPullback_overMap`: Mathlib's `IsPullback.of_iso_pullback`, with the isomorphism
`underlyingSchemeIso θ.abelianIso` onto the fibre product.
`overMap_eq_id`: after `subst`, rigidity gives `θ = (c.pullbackIdIso).symm`, and the
underlying map of `baseChangeIdIso` is the first projection
(`GroupScheme.baseChangeIdIso_hom_left`).
`overMap_comp`: after `subst`, rigidity identifies `θ₃` with
`θ₁ ≫ θ₂.pullback b₁ ≫ (c''.pullbackCompIso b₂ b₁).symm`. Then
`GroupScheme.baseChangeCompIso_inv_fst` and naturality of the first projection for
pulled-back homomorphisms give the composite.

## Provenance

Internal bookkeeping for gluing rigid objects; the mathematical point is that rigidity
makes the chosen isomorphisms satisfy the cocycle condition automatically.
