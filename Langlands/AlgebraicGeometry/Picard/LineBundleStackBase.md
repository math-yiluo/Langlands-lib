# Base cases of descent for module realizations

Module `Langlands.AlgebraicGeometry.Picard.LineBundleStackBase`. This is internal support for
the fpqc stack proof (`Langlands.AlgebraicGeometry.Picard.LineBundleFpqcStackProof`). Let
`F` be a pseudofunctor on schemes with a module realization `R : ModuleRealization F` (see
[`LineBundleStackDictionary`](LineBundleStackDictionary.md)). For `F`, the module proves morphism
descent and effective descent in two base cases: open covers, and single faithfully flat
morphisms. All mathematical input comes from published Library results on modules. The proofs
only translate between Mathlib's descent data and those results.

## Auxiliary module lemmas (namespace `Langlands.AlgebraicGeometry.Picard`)

- `ModCompat f M N φ`: a family of module morphisms `φ i : (f i)^* M ⟶ (f i)^* N` is
  compatible with the composition comparisons `compIso` over every pair `f₁, f₂` from a test
  scheme with `f₁ ≫ f i₁ = f₂ ≫ f i₂`.
- `squarePullbackIso_hom_eq`: the published square comparison `squarePullbackIso` is a
  composite of two `compIso` through a common composite. This restates
  `UnitCocycleDescentUniqueness.squarePullbackIso_hom_eq_compIso` with the module `compIso`.
- `map_pullbackId_hom_app`: the pullback along `f` of the unit comparison
  `Scheme.Modules.pullbackId` is the composition comparison `compIso f (𝟙 Y) f`. It follows
  from Mathlib's `Scheme.Modules.pseudofunctor_left_unitality`.

## Results for a module realization (namespace `ModuleRealization`)

- `isoOfIso`: the isomorphism of `F(X)` given by a module isomorphism.
- `descIso` and `modCompat_descIso`: a morphism of descent data between canonical descent
  data gives module isomorphisms over the members, and these satisfy `ModCompat`. The proof
  applies `μ` to the compatibility of the morphism of descent data (`μ_comp`, `μ_map`,
  `μ_ofObj_hom`).
- `fullyFaithfulToDescentData f H`: `F.toDescentData f` is fully faithful when every
  `ModCompat` family of isomorphisms between pullbacks of two line bundles comes from exactly
  one isomorphism `M ≅ N` (hypothesis `H`). The preimage of a morphism of descent data is the
  descended isomorphism. Uniqueness gives that the preimage of `(F.toDescentData f).map ψ`
  is `ψ`.
- `isPrestackFor_openCover 𝒰` (morphism descent along `𝒰 : X.OpenCover.{u}`): `H` is
  supplied by the published `openCoverIsoGluing_of_homGluing
  OpenCoverHomGluing.openCoverHomGluing`. Its overlap condition, stated with
  `squarePullbackIso`, is the case `q = fst ≫ 𝒰.f i`, `f₁ = fst`, `f₂ = snd` of `ModCompat`.
- `isPrestackFor_singleton p` (morphism descent along a quasi-compact flat surjection `p`):
  `H` is supplied by the published `LineBundleIsoDescent.lineBundleIsoDescent`. Its
  equal-composite condition is the case `q = a ≫ p` of `ModCompat`, translated by
  `equalCompositeIso_hom_eq_compIso`.
- `hom_congr'` and `map_μ_hom`: a descent morphism `D.hom q x₁ x₂` does not depend on how its
  base `q` is written. Its pullback along `g` is `μ` of `D.hom (g ≫ q) y₁ y₂`, conjugated by
  `compIso`. This comes from the descent axiom `pullHom_hom` together with `μ_pullHom`.
- `essSurj_openCover 𝒰` (effective descent along `𝒰 : X.OpenCover.{u}`). Let `D` be a
  descent datum. Its transitions on the pairwise pullbacks (`transition`) are `μIso` of
  `D.hom (fst ≫ 𝒰.f i) fst snd`. `transition_cocycle` proves the published cocycle condition
  `OpenCoverModuleGluing.CocycleCondition`. On the triple overlap, `map_μ_hom` writes each
  pulled-back transition as a `D.hom` between composite maps, and `squarePullbackIso_hom_eq`
  writes each square comparison through `compIso`. The comparisons cancel, and the identity
  becomes `D.hom_comp`. This gives the published gluing data `gluingData 𝒰 D :
  LineBundleGluingData 𝒰`. The glued line bundle `M` is mapped to an object of `F` with
  `ofModule`. The isomorphism `F.toDescentData 𝒰.f M ≅ D` is built with
  `DescentData.isoMk` from the published comparisons `moduleIso i`. Its compatibility over an
  arbitrary test scheme `Y` with `f₁, f₂` is checked after applying `μ`. The descent morphism
  is the pullback of the transition along the lift `ℓ : Y ⟶ 𝒰.X i₁ ×_X 𝒰.X i₂`.
  `tr_transition` computes its transport along `ℓ` from the published `moduleIso_compatible`
  and the Library lemmas `tr_comp`, `tr_map`, `tr_compIso`, `tr_compIso_inv`.
- `essSurj_singleton p` (effective descent along an affine flat surjection `p : X ⟶ Y` with
  `Y` affine). A descent datum `D` along the one-member family `p` gives the equal-composite
  descent datum `datum p D : Datum p (R.mod (D.obj ()))` from `LineBundleFlatDescentStr`.
  Its isomorphisms `θ U a b h` are `μIso (D.hom (a ≫ p) a b)`. Naturality comes from
  `pullHom_hom` and `μ_pullHom` (with `compIso_rfl`), and the cocycle law from `D.hom_comp`.
  The published affine core `exists_str (datum p D) _ (𝟙 Y)` gives a line bundle `N` on `Y`
  with a descended structure `S : Str (datum p D) (𝟙 Y) N`. The object `ofModule N` and the
  isomorphism `p^* N ≅ (𝟙 X)^* (mod D) ≅ mod D`, built from `S.γ X (𝟙 X) p` and
  `Scheme.Modules.pullbackId`, give an isomorphism of descent data. Its compatibility over
  `f₁, f₂` follows from `S.nat` (naturality along `f₁` and `f₂`), `map_pullbackId_hom_app`,
  `S.coc` (compatibility with `θ`) and naturality of `compIso`.
