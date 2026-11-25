/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.FunctorFiniteMatrixCoordinates

/-! # Composition and normalized regular scalar extension
Source: blueprint Compatible isomorphisms, associativity of ordinary scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory MonoidalCategory Limits MonObj
namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S T : C} [monR : MonObj R] [monS : MonObj S] [monT : MonObj T]
  [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) (ψ : S ⟶ T) [IsMonHom φ] [IsMonHom ψ]

/-- The scalar extension composition comparison intertwines the two adjunction units.
Source: extension--restriction adjunction and uniqueness of left adjoints.
(blueprint: lem-pe-regular-extension-composition).
Proof: apply the unit normalization for leftAdjointUniq to the composed adjunction.
Restriction of scalars and its composition comparison have identity underlying maps. -/
theorem extendScalarsComp_unit (M : Mod C R) :
    extendUnitHom (φ ≫ ψ) M ≫ ((extendScalarsComp φ ψ).hom.app M).hom =
      extendUnitHom φ M ≫ extendUnitHom ψ ((extendScalars φ).obj M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (extendRestrictAdjunction (φ ≫ ψ))
    (((extendRestrictAdjunction φ).comp (extendRestrictAdjunction ψ)).ofNatIsoRight
      (comapComp φ ψ).symm) M
  have h' := congrArg Hom.hom h
  simp only [Iso.symm_hom, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, comp_hom', comap_map_hom, comapComp_inv_app_hom,
    extendRestrictAdjunction_unit_app_hom] at h'
  erw [Category.comp_id] at h'
  exact h'

/-- The normalized regular-module comparison respects composition of scalar extensions.
Source: blueprint Compatible isomorphisms, multiplication of adjacent scalars.
(blueprint: lem-pe-regular-extension-composition).
Proof: use injectivity of the extension--restriction adjunction. Naturality of the
second unit moves the first regular comparison through it. Both regular comparisons
then reduce to their coefficient maps, while the composition comparison reduces to
the composite unit. Thus both sides are the same coefficient map φ followed by ψ. -/
theorem regularExtensionIso_comp :
    (extendScalarsComp φ ψ).hom.app (regular R) ≫
      (extendScalars ψ).map (regularExtensionIso φ).hom ≫ (regularExtensionIso ψ).hom =
        (regularExtensionIso (φ ≫ ψ)).hom := by
  apply (extendHomEquiv (φ ≫ ψ) (regular R) (regular T)).injective
  apply hom_ext
  change extendUnitHom (φ ≫ ψ) (regular R) ≫
      ((extendScalarsComp φ ψ).hom.app (regular R)).hom ≫
      ((extendScalars ψ).map (regularExtensionIso φ).hom).hom ≫
      (extendHom ψ (regularCoefficientMap ψ)).hom =
    extendUnitHom (φ ≫ ψ) (regular R) ≫
      (extendHom (φ ≫ ψ) (regularCoefficientMap (φ ≫ ψ))).hom
  rw [← Category.assoc (extendUnitHom (φ ≫ ψ) (regular R)),
    extendScalarsComp_unit, Category.assoc]
  have hn := (extendUnitHom_extendScalarsMap ψ (regularExtensionIso φ).hom).symm
  have hφ : extendUnitHom φ (regular R) ≫ (regularExtensionIso φ).hom.hom = φ :=
    extendUnitHom_extendHom φ (regularCoefficientMap φ)
  have hψ : extendUnitHom ψ (regular S) ≫ (regularExtensionIso ψ).hom.hom = ψ :=
    extendUnitHom_extendHom ψ (regularCoefficientMap ψ)
  have hφψ : extendUnitHom (φ ≫ ψ) (regular R) ≫
      (regularExtensionIso (φ ≫ ψ)).hom.hom = φ ≫ ψ :=
    extendUnitHom_extendHom (φ ≫ ψ) (regularCoefficientMap (φ ≫ ψ))
  change _ = extendUnitHom (φ ≫ ψ) (regular R) ≫
    (regularExtensionIso (φ ≫ ψ)).hom.hom
  erw [← Category.assoc (extendUnitHom ψ ((extendScalars φ).obj (regular R))), ← hn]
  change extendUnitHom φ (regular R) ≫
      ((regularExtensionIso φ).hom.hom ≫ extendUnitHom ψ (regular S)) ≫
        (regularExtensionIso ψ).hom.hom = _
  erw [Category.assoc ((regularExtensionIso φ).hom.hom), hψ,
    ← Category.assoc (extendUnitHom φ (regular R)), hφ, hφψ]

/-- The normalized free-basis comparison respects successive scalar extensions.
Source: blueprint Compatible isomorphisms, use the same integral basis at both levels.
(blueprint: lem-pe-regular-extension-composition).
Proof: naturality moves the initial basis map through extendScalarsComp. Move the
first sum of regular comparisons through the second biproduct comparison, and
combine the two functor biproduct comparisons. Naturality in the composition
comparison moves it to the entries. Each entry is regularExtensionIso_comp, so
biproduct extensionality identifies the resulting sums. -/
theorem regularFreeComparison_comp
    [Preadditive (Mod C R)] [Preadditive (Mod C S)] [Preadditive (Mod C T)]
    [HasFiniteBiproducts (Mod C R)] [HasFiniteBiproducts (Mod C S)]
    [HasFiniteBiproducts (Mod C T)]
    [(extendScalars φ).Additive] [(extendScalars ψ).Additive]
    [(extendScalars (φ ≫ ψ)).Additive]
    {I : Type} [Finite I] (M : Mod C R) (e : M ≅ ⨁ fun _ : I ↦ regular R) :
    let F := extendScalars φ
    let G := extendScalars ψ
    let H := extendScalars (φ ≫ ψ)
    let b₁ := F.mapIso e ≪≫ F.mapBiproduct (fun _ : I ↦ regular R) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso φ)
    let b₂ := G.mapBiproduct (fun _ : I ↦ regular S) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso ψ)
    let b₀ := H.mapIso e ≪≫ H.mapBiproduct (fun _ : I ↦ regular R) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso (φ ≫ ψ))
    (extendScalarsComp φ ψ).hom.app M ≫ G.map b₁.hom ≫ b₂.hom = b₀.hom := by
  let F := extendScalars φ
  let G := extendScalars ψ
  let H := extendScalars (φ ≫ ψ)
  let cmp := (extendScalarsComp φ ψ).hom
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, biproduct.mapIso_hom]
  simp only [Functor.map_comp, biproduct.mapIso_hom, Category.assoc]
  have hn := cmp.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc (cmp.app M), ← hn]
  simp only [Category.assoc]
  erw [reassoc_of% (Functor.mapBiproduct_map G
    (fun _ : I ↦ (regularExtensionIso φ).hom))]
  have hc := congrArg Iso.hom (Functor.mapBiproduct_composite F G
    (fun _ : I ↦ regular R))
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hc
  erw [← reassoc_of% hc]
  erw [reassoc_of% (Functor.mapBiproduct_natTrans H (F ⋙ G) cmp
    (fun _ : I ↦ regular R))]
  simp only [← Functor.biproduct_map_comp]
  congr 2
  congr 1
  funext i
  exact regularExtensionIso_comp φ ψ

/-- Transport of a normalized free comparison along equality of coefficient maps.
Source: blueprint Compatible isomorphisms, quotient factorization.
(blueprint: lem-pe-regular-extension-composition).
Proof: substitute the equality of coefficient maps. Both functors and both normalized
comparisons then coincide, and transport is the identity by proof irrelevance. -/
theorem regularFreeComparison_eq
    {χ χ' : R ⟶ T} [IsMonHom χ] [IsMonHom χ']
    (hχ : χ = χ') (hF : extendScalars χ = extendScalars χ')
    [Preadditive (Mod C R)] [Preadditive (Mod C T)]
    [HasFiniteBiproducts (Mod C R)] [HasFiniteBiproducts (Mod C T)]
    [(extendScalars χ).Additive] [(extendScalars χ').Additive]
    {I : Type} [Finite I] (M : Mod C R) (e : M ≅ ⨁ fun _ : I ↦ regular R) :
    (eqToIso hF).hom.app M ≫
      ((extendScalars χ').mapIso e ≪≫
        (extendScalars χ').mapBiproduct (fun _ : I ↦ regular R) ≪≫
          biproduct.mapIso (fun _ : I ↦ regularExtensionIso χ')).hom =
      ((extendScalars χ).mapIso e ≪≫
        (extendScalars χ).mapBiproduct (fun _ : I ↦ regular R) ≪≫
          biproduct.mapIso (fun _ : I ↦ regularExtensionIso χ)).hom := by
  subst χ'
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- Successive normalized finite free comparisons respect the transported balancing map.
Source: blueprint Compatible isomorphisms, ordinary balancing in fixed integral bases.
(blueprint: lem-pe-regular-extension-composition).
Proof: precompose with extendScalarsComp. Its inverse cancels the balancing map.
The composition identity and transport identity identify the remaining comparisons. -/
theorem regularFreeComparison_balancing
    {χ : R ⟶ T} [IsMonHom χ]
    (hχ : φ ≫ ψ = χ) (hF : extendScalars (φ ≫ ψ) = extendScalars χ)
    [Preadditive (Mod C R)] [Preadditive (Mod C S)] [Preadditive (Mod C T)]
    [HasFiniteBiproducts (Mod C R)] [HasFiniteBiproducts (Mod C S)]
    [HasFiniteBiproducts (Mod C T)]
    [(extendScalars φ).Additive] [(extendScalars ψ).Additive]
    [(extendScalars (φ ≫ ψ)).Additive] [(extendScalars χ).Additive]
    {I : Type} [Finite I] (M : Mod C R) (e : M ≅ ⨁ fun _ : I ↦ regular R) :
    let F := extendScalars φ
    let G := extendScalars ψ
    let H := extendScalars χ
    let b₁ := F.mapIso e ≪≫ F.mapBiproduct (fun _ : I ↦ regular R) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso φ)
    let b₂ := G.mapBiproduct (fun _ : I ↦ regular S) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso ψ)
    let b₀ := H.mapIso e ≪≫ H.mapBiproduct (fun _ : I ↦ regular R) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso χ)
    G.map b₁.hom ≫ b₂.hom =
      ((extendScalarsComp φ ψ).symm ≪≫ eqToIso hF).hom.app M ≫ b₀.hom := by
  let cmp := extendScalarsComp φ ψ
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  apply (cancel_epi (cmp.hom.app M)).1
  simp only [Category.assoc]
  rw [← Category.assoc (cmp.hom.app M) (cmp.inv.app M),
    cmp.hom_inv_id_app, Category.id_comp]
  exact (regularFreeComparison_comp φ ψ M e).trans
    (regularFreeComparison_eq hχ hF M e).symm

/-- The scalar extension comparison of a chosen finite regular basis.
Source: blueprint Compatible isomorphisms, finite free ordinary scalar extension.
(blueprint: lem-pe-regular-extension-composition). -/
def regularFreeExtensionIso
    [Preadditive (Mod C R)] [Preadditive (Mod C S)]
    [HasFiniteBiproducts (Mod C R)] [HasFiniteBiproducts (Mod C S)]
    [(extendScalars φ).Additive]
    {I : Type} [Finite I] {M : Mod C R} (e : M ≅ ⨁ fun _ : I ↦ regular R) :
    (extendScalars φ).obj M ≅ ⨁ fun _ : I ↦ regular S :=
  (extendScalars φ).mapIso e ≪≫
    (extendScalars φ).mapBiproduct (fun _ : I ↦ regular R) ≪≫
      biproduct.mapIso (fun _ : I ↦ regularExtensionIso φ)

/-- The named finite basis comparison respects transported ordinary balancing.
Source: blueprint Compatible isomorphisms, the same bases at adjacent levels.
(blueprint: lem-pe-regular-extension-composition).
Proof: expand the two named comparisons and apply regularFreeComparison_balancing. -/
theorem regularFreeExtensionIso_balancing
    {χ : R ⟶ T} [IsMonHom χ]
    (hχ : φ ≫ ψ = χ) (hF : extendScalars (φ ≫ ψ) = extendScalars χ)
    [Preadditive (Mod C R)] [Preadditive (Mod C S)] [Preadditive (Mod C T)]
    [HasFiniteBiproducts (Mod C R)] [HasFiniteBiproducts (Mod C S)]
    [HasFiniteBiproducts (Mod C T)]
    [(extendScalars φ).Additive] [(extendScalars ψ).Additive]
    [(extendScalars (φ ≫ ψ)).Additive] [(extendScalars χ).Additive]
    {I : Type} [Finite I] {M : Mod C R} (e : M ≅ ⨁ fun _ : I ↦ regular R) :
    (extendScalars ψ).map (regularFreeExtensionIso φ e).hom ≫
        ((extendScalars ψ).mapBiproduct (fun _ : I ↦ regular S) ≪≫
          biproduct.mapIso (fun _ : I ↦ regularExtensionIso ψ)).hom =
      ((extendScalarsComp φ ψ).symm ≪≫ eqToIso hF).hom.app M ≫
        (regularFreeExtensionIso χ e).hom := by
  exact regularFreeComparison_balancing φ ψ hχ hF M e

end CategoryTheory.Mod
