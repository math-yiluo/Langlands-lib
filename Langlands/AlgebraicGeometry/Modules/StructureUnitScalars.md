# Global units as automorphisms of the structure module

For an arbitrary scheme `X : AlgebraicGeometry.Scheme.{u}`, this module identifies
the automorphisms of the structure module

```
structureModule X = SheafOfModules.unit X.ringCatSheaf
```

(published in `Langlands.AlgebraicGeometry.Modules.SectionLocus`) with the units of
the global section ring `Γ(X, ⊤)`. It also proves that the identification is natural
under pullback along every scheme morphism. All names are in the namespace
`Langlands.SchemeModule`. Every declaration holds for an arbitrary universe and
arbitrary schemes, with no hypotheses on `X`, `Y` or `f`.

## Endomorphisms of the structure module

For `φ : structureModule X ⟶ structureModule X` and an open `U : X.Opens`,

```
structureEndValue φ U : Γ(X, U) := φ.app U 1
```

is the image of `1` under the component of `φ` on `U`. It is read as an element of
the ring `Γ(X, U)`. The definition is needed because the carrier of
`Γ(structureModule X, U)` is the ring `Γ(X, U)` only up to definitional unfolding.
The basic lemmas are:

- `structureEnd_app_eq_mul`: `φ.app U a = a * structureEndValue φ U`. This is
  linearity of `φ.app U` applied to `a • 1`.
- `structureEndValue_eq_res`: `structureEndValue φ U` is the restriction to `U` of
  `structureEndValue φ ⊤`. This follows from naturality of `φ` and the fact that
  restriction sends `1` to `1`.
- `structureEnd_app_eq_mul_res`: `φ.app U a = a * res_U (structureEndValue φ ⊤)`,
  where `res_U` is `X.presheaf.map (homOfLE le_top).op`.
- `structureEnd_ext`: two endomorphisms with equal global values at one are equal.
- `structureEndValue_comp`: `structureEndValue (φ ≫ ψ) U` is the product
  `structureEndValue φ U * structureEndValue ψ U`.
- `structureEndValue_id`: the identity has value `1`.

`structureMulHom r`, for `r : Γ(X, ⊤)`, is the published
`sectionHom (structureModule X) r`. This is the morphism that Mathlib's
`SheafOfModules.unitHomEquiv` assigns to the family of restrictions of `r`.
`structureEndValue_mulHom` shows that its global value at one is `r`, and
`structureMulHom_app` shows that it acts on `U` by multiplication with the
restriction of `r`.

## Automorphisms and global units

- `structureAutScalar e : Γ(X, ⊤)ˣ` is the unit of an automorphism `e`. Its value is
  `e.hom.app ⊤ 1` and its inverse is `e.inv.app ⊤ 1`. These are the definitional
  lemmas `structureAutScalar_val` and `structureAutScalar_inv_val`. The two unit
  equations come from `e.hom_inv_id`, `e.inv_hom_id` and `structureEndValue_comp`.
- `structureAutScalar_hom_app`: on every open `U`, `e.hom.app U a` is `a` times the
  restriction to `U` of `structureAutScalar e`.
- `structureAutScalar_inv_app`: on every open `U`, `e.inv.app U a` is `a` times the
  restriction to `U` of `(structureAutScalar e)⁻¹`.
- `structureAutOfUnit r` is the inverse construction for a global unit `r`. Its
  forward map is `structureMulHom r` and its inverse is `structureMulHom r⁻¹`
  (lemmas `structureAutOfUnit_hom` and `structureAutOfUnit_inv`). The local formulas
  are `structureAutOfUnit_hom_app` and `structureAutOfUnit_inv_app`.
- Inverse laws: `structureAutScalar_ofUnit` gives
  `structureAutScalar (structureAutOfUnit r) = r`, and `structureAutOfUnit_scalar`
  gives `structureAutOfUnit (structureAutScalar e) = e`. The second law is proved
  with `structureEnd_ext`.
- `structureAutUnitsEquiv : (structureModule X ≅ structureModule X) ≃ Γ(X, ⊤)ˣ`
  bundles these maps. Its simp lemmas are `structureAutUnitsEquiv_apply` and
  `structureAutUnitsEquiv_symm_apply`.
- Identity, composition, inverse and injectivity:
  `structureAutScalar_refl` (scalar `1`), `structureAutScalar_trans`
  (`structureAutScalar (e ≪≫ e') = structureAutScalar e * structureAutScalar e'`),
  `structureAutScalar_symm` (`structureAutScalar e.symm = (structureAutScalar e)⁻¹`),
  and `structureAutScalar_injective`.
- `structureAutMulEquiv : Aut (structureModule X) ≃* Γ(X, ⊤)ˣ` is the same map as a
  group isomorphism. In `Aut`, the product `e * e'` is `e' ≪≫ e`. Its compatibility
  with multiplication therefore uses `structureAutScalar_trans` together with
  commutativity of `Γ(X, ⊤)`. Its simp lemmas are `structureAutMulEquiv_apply` and
  `structureAutMulEquiv_symm_apply`.

## Naturality under pullback

For a scheme morphism `f : X ⟶ Y` and an automorphism `e` of `structureModule Y`,

```
structureAutPullback f e :=
  (pullbackUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f
```

is the automorphism of `structureModule X` obtained by conjugating the pullback of
`e` with the published canonical comparison
`Langlands.Scheme.Modules.pullbackUnitIso f : f^* 𝒪_Y ≅ 𝒪_X`.
`structureAutPullback_hom` writes out its forward morphism.

The main naturality theorem is

```
structureAutScalar_pullback f e :
  structureAutScalar (structureAutPullback f e) =
    Units.map f.appTop.hom.toMonoidHom (structureAutScalar e).
```

The ring map is the actual global-sections map `f.appTop : Γ(Y, ⊤) ⟶ Γ(X, ⊤)` of
the morphism `f`. No compatibility hypothesis is assumed. The theorem follows from
the stronger lemma `structureAutPullback_eq_ofUnit`, which says that
`structureAutPullback f e` equals `structureAutOfUnit` of that unit.

Proof of `structureAutPullback_eq_ofUnit`. By `Iso.ext` and `Iso.inv_comp_eq`, it is
enough to show

```
pullback.map e.hom ≫ (pullbackUnitIso f).hom = (pullbackUnitIso f).hom ≫ (structureAutOfUnit _).hom.
```

The hom-equivalence of `Scheme.Modules.pullbackPushforwardAdjunction f` is injective,
so we apply it to both sides. Its naturality in each variable, together with the
published characterization `Langlands.Scheme.Modules.pullbackUnitAdjunction` (the
adjoint of `(pullbackUnitIso f).hom` is `unitToPushforwardUnit f`), turns the
equation into

```
e.hom ≫ unitToPushforwardUnit f
  = unitToPushforwardUnit f ≫ pushforward.map (structureAutOfUnit _).hom
```

between morphisms of sheaves of modules on `Y`. The proof uses `erw` for this
rewrite. After the naturality rewrites, one hom-equivalence is indexed by
`structureModule Y` instead of `SheafOfModules.unit Y.ringCatSheaf`, and the two
agree only after unfolding. The equation is checked on sections over each open `U`
of `Y`.
`unitToPushforwardUnit f` acts there as `f.app U`, by Mathlib's definition of
`SheafOfModules.unitToPushforwardObjUnit`. The local multiplication formulas and
multiplicativity of `f.app U` reduce the goal to the equality of
`f.app U (res_U s)` with the restriction to `f ⁻¹ᵁ U` of `f.appTop s`, where `s`
is the global unit of `e`. This is `Scheme.Hom.naturality` for the inclusion
`U ≤ ⊤`.

The file sets `backward.isDefEq.respectTransparency false`, following the published
`Langlands.AlgebraicGeometry.Modules.UnitEndResidueStalkProof`. This lets the
`change` steps identify sections of `structureModule X` with elements of `Γ(X, U)`.

## Provenance and scope

This is an internal derived interface for the actual module categories in Mathlib.
It specializes the standard identification `Hom_{𝒪_X}(𝒪_X, 𝓕) = Γ(X, 𝓕)`, which is
Mathlib's `SheafOfModules.unitHomEquiv`, to `𝓕 = 𝒪_X` and restricts it to
automorphisms. Its dependencies are Mathlib and the published Library modules
`Langlands.AlgebraicGeometry.Modules.SectionLocus` (`structureModule`, `sectionHom`,
`sectionFamily`), `Langlands.AlgebraicGeometry.Modules.PullbackUnit`
(`pullbackUnitIso`, `unitToPushforwardUnit`) and
`Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs` (`pullbackUnitAdjunction`).
The module was written as a prerequisite of the intrinsic-character task
`cda49074-0684-4906-b5cb-3c42024c36d4`. That task's motivation from EGM Chapter VII,
7.3–7.4, is not claimed to contain this Lean API. The module constructs no character
or kernel and makes no claim about invertible modules beyond `𝒪_X` itself. Similar
scalar helpers in `LineBundleFrameOpen` and `UnitEndResidueStalkProof` are private
and remain unchanged.
