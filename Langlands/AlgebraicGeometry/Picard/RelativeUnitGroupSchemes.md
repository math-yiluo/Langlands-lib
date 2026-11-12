# Group schemes of relative global units and their quotient along a finite subscheme

Module `Langlands.AlgebraicGeometry.Picard.RelativeUnitGroupSchemes`, namespace
`Langlands.AlgebraicGeometry.Picard.RelativeUnitGroupSchemes`.

This is an internal construction for the proof of
`Langlands.AlgebraicGeometry.Picard.FieldEtaleFppfClassSheafStatement`. For `f : X ⟶ S` the
published presheaf `RelativeGlobalUnits.groupPresheaf f` sends a test `T : Over S` to the
global units `Γ(T ×_S X, ⊤)ˣ`, with restriction given by pulling back functions
(`RelativeGlobalUnits.restriction`). The Library represents it, for proper schemes over a
field, by the determinant-open scheme `PicardGroupoid.fieldUnitScheme f` together with the
natural isomorphism `PicardGroupoid.fieldUnitSchemeIso f`. This module turns these
representing objects into group schemes and builds the quotient used by the rigidification
argument.

## Generic part

Data: `f : X ⟶ S`, an object `U : Over S` and a natural isomorphism
`e : schemeYoneda U ≅ RelativeGlobalUnits.presheaf f`.

- `groupPresheaf f` is the unit presheaf as a presheaf of groups.
- `representableBy f U e` is the representation of that presheaf by `U` obtained from `e`.
- `group f U e : GroupScheme S` is `U` with the group object structure from Mathlib's
  `GrpObj.ofRepresentableBy`.
- `pointsEquiv f U e T : (T ⟶ U) ≃* Γ(T ×_S X, ⊤)ˣ` is the group isomorphism on points
  (multiplicativity from Mathlib's `yonedaGrpObjIsoOfRepresentableBy`), and
  `pointsEquiv_comp` says it turns precomposition into `RelativeGlobalUnits.restriction`.
- For a second such datum `(f', U', e')` and a natural transformation
  `β : groupPresheaf f ⟶ groupPresheaf f'` (published `CommGrpCat`-valued presheaves),
  `pointsNatTrans` is the induced transformation of point groups and `hom f U e U' e' β` the
  homomorphism of group schemes given by full faithfulness of Mathlib's `yonedaGrp`.
  `pointsEquiv_comp_hom` states `pointsEquiv' (x ≫ hom) = β (pointsEquiv x)`.

## Over a field

Let `k` be a field and `f : X ⟶ Spec k` proper.

- `fieldGroup f` is `group f (fieldUnitScheme f) (fieldUnitSchemeIso f)`, and
  `fieldPointsEquiv f T` its points isomorphism.
- `fieldGroup_smooth` (published `fieldUnitScheme_smooth`), `fieldGroup_isAffine`,
  `fieldGroup_nonempty` (the unit point over `Spec k`), and `fieldGroup_connectedSpace`. The
  last uses `candidate_connectedSpace`: the coordinate ring of the determinant-open candidate
  is the localization of a polynomial ring at the determinant; if the candidate is nonempty the
  determinant is nonzero, so the ring is a domain and the spectrum is irreducible.

Now let also `g : Z ⟶ Spec k` be proper and `z : Z ⟶ X` with `hz : z ≫ f = g`. The morphism
`SubschemeRigidification.zRel f g z hz` (from `SubschemeRigidifiedClasses`) gives maps
`T ×_k Z ⟶ T ×_k X`.

- `unitsNatTrans f g z hz` pulls global units back along these maps; naturality is the
  naturality of `zRel` on global functions.
- `unitsHom f g z hz : fieldGroup f ⟶ fieldGroup g` is the induced homomorphism, with
  `pointsEquiv_unitsHom` giving its effect on points.
- `mono_unitsHom`: if every `((zRel f g z hz).app T).appTop` is injective, the underlying
  morphism of `unitsHom` is a monomorphism (checked on points).
- `range_unitsHom_isNormal`: its range is normal, since the points form commutative groups.

`exists_quotient` assumes the injectivity hypothesis
`∀ T, Function.Injective ((zRel f g z hz).app T).appTop` and produces a group scheme `Q` over
`Spec k` and `q : fieldGroup g ⟶ Q` such that `Q` is smooth and affine over `k`, the scheme
morphism of `q` is flat, surjective, locally of finite presentation, affine and smooth, and for
every test `T` and point `h : T ⟶ (fieldGroup g).X`,

```
h ≫ q.hom.hom = 1 ↔ fieldPointsEquiv g T h ∈ range (Units.map ((zRel f g z hz).app T).appTop)
```

that is, `h` lies in the kernel of `q` exactly when the corresponding unit of `T ×_k Z` comes
from a unit of `T ×_k X`. The proof: `unitsHom` is a closed subgroup embedding by the published
`HomImage.isClosedSubgroup_of_mono` (its source is smooth, connected and affine); the published
`normalSubgroupQuotient` gives `Q` and `q` with `IsFppfQuotient (range unitsHom) q`; smoothness
of `q` follows from the published `IsFppfQuotient.smooth_of_smooth_kernel` because the kernel is
represented by the smooth `fieldGroup f`; the kernel description uses the published
`mem_range_kernelι_iff`.

## Provenance

Internal. Representing the unit functor by a group scheme and dividing the units of a finite
subscheme by those of `X` is the standard construction of the group acting on rigidifications
in the theory of Picard functors. The formalization uses only published Library results and
Mathlib.
