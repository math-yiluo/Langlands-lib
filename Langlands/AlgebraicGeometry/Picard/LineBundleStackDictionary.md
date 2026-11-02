# Module realizations of pseudofunctors of line bundles

Module `Langlands.AlgebraicGeometry.Picard.LineBundleStackDictionary`. This is internal
support for the fpqc stack proof
(`Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof`). It translates descent data
of the line-bundle pseudofunctor into statements about module sheaves and their pullback
comparisons, which is the language of the Library's descent results. The definitions are
internal bookkeeping devices with no counterpart in the literature.

## The structure `ModuleRealization F`

For a pseudofunctor `F : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}`, a
`ModuleRealization F` consists of the following data.

- `mod : F(X) → X.Modules` and `modHom : (M ⟶ N) → (mod M ⟶ mod N)`. `modHom` is
  functorial (`modHom_comp`, `modHom_id`), injective (`modHom_injective`), and takes values
  in isomorphisms (`isIso_modHom`).
- `ofIso`, which turns every module isomorphism `mod M ≅ mod N` into a morphism `M ⟶ N` with
  `modHom (ofIso e) = e.hom`. So morphisms of `F(X)` are exactly the isomorphisms of the
  underlying modules.
- `rankOne`: every `mod M` is locally free of rank one (`IsLocallyFreeRankOne`).
- `ofModule L hL` with `ofModuleIso : mod (ofModule L hL) ≅ L`: every line bundle underlies
  an object.
- `mapIso f M : mod (f^* M) ≅ (Scheme.Modules.pullback f).obj (mod M)`, identifying the
  pullback in `F` with the module pullback. `modHom_map` says that `F.map f` acts on
  morphisms by module pullback, conjugated by `mapIso`.
- `modHom_mapComp'_hom` says that the composition comparison `F.mapComp'` acts as the
  inverse of the module composition comparison `compIso g u u' h` of
  `Langlands.Scheme.Modules`, conjugated by `mapIso`.

The base cases of the fpqc proof are proved for an arbitrary `F` with a module realization
and then applied to `PicardGroupoid.pseudofunctor`. With `F` an abstract variable, the
kernel never unfolds the concrete pseudofunctor when it checks those proofs. Statements
about the concrete pseudofunctor that mix its descent-data forms with module pullbacks
otherwise make kernel checking very slow.

## Module forms of morphisms between pullbacks (namespace `ModuleRealization`)

For `φ : f₁^* M₁ ⟶ f₂^* M₂` in `F(Y)`, the module form is
`μ φ = (mapIso f₁ M₁).inv ≫ modHom φ ≫ (mapIso f₂ M₂).hom`, a morphism
`f₁^* (mod M₁) ⟶ f₂^* (mod M₂)` of module sheaves. `μIso` is the corresponding isomorphism
and `modIso φ` is `modHom φ` as an isomorphism. The following lemmas are proved:

- `μ_comp`, `μ_id`, `μ_injective`: `μ` is functorial and injective;
- `μ_map`: `μ (f^*φ) = (Scheme.Modules.pullback f).map (modHom φ)`;
- `μ_pullHom`: `μ (pullHom φ g gf₁ gf₂ h₁ h₂) = tr g h₁ h₂ (μ φ)`. Here `pullHom` is
  Mathlib's pullback of morphisms between pullbacks, and `tr` is the transport of module
  morphisms from `Langlands.Scheme.Modules.LineBundleFlatDescent`. Both conjugate a pulled-back
  morphism by composition comparisons;
- `μ_ofObj_hom` and `μ_toDescentData_obj_hom`: the descent morphisms of the canonical descent
  datum of an object `M` over `S` are the module composition comparisons
  `compIso f₁ (f i₁) q _ (mod M) ≫ (compIso f₂ (f i₂) q _ (mod M)).inv`, conjugated by `mapIso`;
- `modHom_mapComp'_inv`: the inverse composition comparison of `F` is the module composition
  comparison, conjugated by `mapIso`.

## The realization of the line-bundle pseudofunctor (namespace `PicardGroupoid`)

`PicardGroupoid.moduleRealization : ModuleRealization pseudofunctor` takes `mod M = M.of.obj`
(the underlying module of a line bundle) and `modHom φ = φ.iso.hom.hom`. All identifications
`mapIso` and `ofModuleIso` are identities. This works because the published pseudofunctor
pulls back line bundles by the ordinary module pullback. The only nontrivial field is
`modHom_mapComp'_hom`. Its concrete version, `PicardGroupoid.modHom_mapComp'_hom`, states
that the composition comparison of `PicardGroupoid.pseudofunctor` has underlying module map
`(compIso g u u' h (mod M)).inv`. It is proved by substituting `u' = g ≫ u`, rewriting
`compIso` with `compIso_rfl` as Mathlib's `Scheme.Modules.pullbackComp`, and unfolding the
published composition comparison `PicardGroupoid.pullbackComp`.
