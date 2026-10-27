# Tensor products of free Yoneda module presheaves on opens

For a scheme `X : AlgebraicGeometry.Scheme.{u}` (arbitrary universe `u`) and
opens `V W : X.Opens`, write

```
A(V) = (PresheafOfModules.free X.ringCatSheaf.obj).obj (CategoryTheory.yoneda.obj V)
```

for the free presheaf of `𝒪_X`-modules on the Yoneda presheaf of `V`. Its
sections over an open `U` form the free `𝒪_X(U)`-module with basis
`ModuleCat.freeMk k`, indexed by the arrows `k : U ⟶ V`, so there is one basis
element when `U ≤ V` and none otherwise. This module, in namespace
`Langlands.Scheme.Modules`, constructs the isomorphism

```
freeYonedaInfTensorIso V W : A(V ⊓ W) ≅ A(V) ⊗ A(W)
```

of presheaves of modules. It proves the component formulas for both directions
and an extensionality lemma for maps out of `A(V) ⊗ A(W)`. There are no
hypotheses on `X`, `V` or `W`: no flatness, sheaf, or affineness assumption.

The tensor product is the sectionwise tensor product of presheaves of modules
over the commutative ring presheaf `X.presheaf`. It comes from the file-local
instance `freeYonedaTensorMonoidalCategory`, whose value is the same as that of
the local instance in the published `PresheafPullbackTensor` module:
`inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))`.
The instance has an explicit name because an unnamed one would generate
auxiliary declaration names that already exist in the published `Tensor` module,
and the two modules could then not be imported together. The sections of
`A(V) ⊗ A(W)` over `U` are `A(V)(U) ⊗[𝒪_X(U)] A(W)(U)`. Restriction acts on pure
tensors factorwise (`PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul`).

## Construction

1. `opensHomInfEquiv U V W : (U ⟶ V ⊓ W) ≃ (U ⟶ V) × (U ⟶ W)`
   sends `k` to `(k ≫ homOfLE inf_le_left, k ≫ homOfLE inf_le_right)`.
   It sends a pair `(i, j)` back to `homOfLE (le_inf (leOfHom i) (leOfHom j))`.
   Arrows between opens are subsingletons (the opens form a poset), so both
   inverse laws hold by `Subsingleton.elim`.

2. `freeYonedaInfTensorIsoApp V W U` is the isomorphism of sections over `U`.
   It is the composite
   ```
   (ModuleCat.free 𝒪_X(U)).mapIso (opensHomInfEquiv U V W).toIso
     ≪≫ (ModuleCat.FreeMonoidal.μIso 𝒪_X(U) (U ⟶ V) (U ⟶ W)).symm.
   ```
   The first factor is the free-module functor applied to the bijection of
   step 1, viewed as an isomorphism of types. The second is the inverse of
   Mathlib's isomorphism `free(S) ⊗ free(T) ≅ free(S × T)`. On basis elements,
   `μIso` sends `freeMk s ⊗ₜ freeMk t` to `freeMk (s, t)`
   (`ModuleCat.FreeMonoidal.μIso_hom_freeMk_tmul_freeMk`), and its inverse sends
   `freeMk (s, t)` back to `freeMk s ⊗ₜ freeMk t`
   (`ModuleCat.FreeMonoidal.μIso_inv_freeMk`).
   Both factors are isomorphisms, so their inverse laws are the inverse laws of
   `freeYonedaInfTensorIsoApp`. No separate inverse law needs proving.

3. `freeYonedaInfTensorIso V W` is `PresheafOfModules.isoMk` applied to these
   sectionwise isomorphisms. `isoMk` uses the sectionwise inverses as the
   components of the inverse map and derives their naturality and both inverse
   identities from the sectionwise ones. The only proof obligation is
   naturality of the hom.

   For `f : U ⟶ U'` in `X.Opensᵒᵖ`, the two composites are compared on basis
   elements `freeMk k` with `k : U.unop ⟶ V ⊓ W`, using
   `ModuleCat.free_hom_ext`. The helper `freeYoneda_map_freeMk` says that
   restriction along `f` sends `freeMk k` to `freeMk (f.unop ≫ k)`. Its proof
   unfolds `PresheafOfModules.free` and uses `ModuleCat.freeDesc_apply`.
   Restricting first and then applying the comparison gives
   `freeMk ((f.unop ≫ k) ≫ ι_V) ⊗ₜ freeMk ((f.unop ≫ k) ≫ ι_W)`, where
   `ι_V = homOfLE inf_le_left` and `ι_W = homOfLE inf_le_right`. Applying the
   comparison first and then restricting factorwise gives
   `freeMk (f.unop ≫ k ≫ ι_V) ⊗ₜ freeMk (f.unop ≫ k ≫ ι_W)`. These agree by
   associativity of composition.

## Component formulas

- `freeYonedaInfTensorIsoApp_hom_freeMk` and
  `freeYonedaInfTensorIso_hom_app_freeMk`: for `U` and `k : U.unop ⟶ V ⊓ W`,
  ```
  (freeYonedaInfTensorIso V W).hom.app U (freeMk k)
    = freeMk (k ≫ homOfLE inf_le_left) ⊗ₜ freeMk (k ≫ homOfLE inf_le_right).
  ```
  Proof: `ModuleCat.free_map_apply`, then `μIso_inv_freeMk`.

- `freeYonedaInfTensorIso_hom_app_id`: the required formula at the identity
  basis section,
  ```
  (freeYonedaInfTensorIso V W).hom.app (op (V ⊓ W)) (freeMk (𝟙 (V ⊓ W)))
    = freeMk (homOfLE (inf_le_left : V ⊓ W ≤ V)) ⊗ₜ
        freeMk (homOfLE (inf_le_right : V ⊓ W ≤ W)).
  ```
  Proof: the general formula with `k = 𝟙`. The composites `𝟙 ≫ ι` and `ι` are
  then equal by `rfl`.

- `freeYonedaInfTensorIsoApp_inv_freeMk_tmul` and
  `freeYonedaInfTensorIso_inv_app_freeMk_tmul`: for `i : U.unop ⟶ V` and
  `j : U.unop ⟶ W`,
  ```
  (freeYonedaInfTensorIso V W).inv.app U (freeMk i ⊗ₜ freeMk j)
    = freeMk (homOfLE (le_inf (leOfHom i) (leOfHom j))).
  ```
  Proof: `μIso_hom_freeMk_tmul_freeMk`, then `ModuleCat.free_map_apply`.

## Extensionality

- `freeYonedaEquiv_eq_app_freeMk_id`: for a map
  `m : A(V) ⟶ M` into a presheaf of modules `M : X.PresheafOfModules`, Mathlib's
  `PresheafOfModules.freeYonedaEquiv m` equals `m.app (op V) (freeMk (𝟙 V))`.
  Proof: `PresheafOfModules.freeYonedaEquiv_symm_app` applied to
  `freeYonedaEquiv m`, followed by `Equiv.symm_apply_apply`.

- `freeYonedaTensor_hom_ext`: let `f g : A(V) ⊗ A(W) ⟶ M` be maps into any
  presheaf of modules `M`. Suppose their components at `op (V ⊓ W)` agree on
  `freeMk (homOfLE inf_le_left) ⊗ₜ freeMk (homOfLE inf_le_right)`. Then
  `f = g`. Proof: cancel the epimorphism `(freeYonedaInfTensorIso V W).hom` on
  the left. Then apply injectivity of `freeYonedaEquiv` on maps out of
  `A(V ⊓ W)`. `PresheafOfModules.freeYonedaEquiv_comp` turns
  `freeYonedaEquiv (iso.hom ≫ f)` into `f.app _ (freeYonedaEquiv iso.hom)`.
  The two lemmas above identify `freeYonedaEquiv iso.hom` with the tensor of
  the two inclusion basis sections. The hypothesis then closes the goal.

## Provenance

This is an internal derivation from the pinned Mathlib and transcribes no
external theorem. It is the sectionwise calculation that the free module on a
product of sets is the tensor product of the free modules. Because arrows
between opens are subsingletons, the basis of `A(V)(U) ⊗ A(W)(U)` is indexed by
pairs of inclusions `U ≤ V`, `U ≤ W`, which correspond to the single inclusion
`U ≤ V ⊓ W`. The module was built for the free-generator case of the presheaf
pullback tensor comparison (task b45cacfc), which compares maps by their value
at the intersection generator. It imports only
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal` and
`Mathlib.AlgebraicGeometry.Modules.Presheaf`. The last one supplies
`X.ringCatSheaf` and `X.PresheafOfModules`.
