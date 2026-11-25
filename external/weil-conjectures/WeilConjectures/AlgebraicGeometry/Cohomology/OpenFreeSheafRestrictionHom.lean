/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisFreeComplex
/-! # Restriction of morphisms from a represented open

Source: Stacks Project, Tags 03DI, 03DJ, 04J0, and Section 01F7.
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt
private noncomputable def freeSectionsEquiv {X : Scheme.{u}} (W : X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (H.openFreeSheaf W ⟶ F) ≃ F.obj.obj (Opposite.op W) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).homEquiv
    (yoneda.obj W ⋙ AddCommGrpCat.free) F).trans
      (((AddCommGrpCat.adj.whiskerRight X.Opensᵒᵖ).homEquiv _ _).trans yonedaEquiv)

private theorem freeSectionsEquiv_naturality {X : Scheme.{u}} (W : X.Opens)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G)
    (a : H.openFreeSheaf W ⟶ F) :
    freeSectionsEquiv W G (a ≫ f) =
      f.hom.app (Opposite.op W) (freeSectionsEquiv W F a) := by
  dsimp only [freeSectionsEquiv, Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

/-- Restriction is bijective on morphisms out of the free sheaf of the image open.
Source: Stacks Project, Tags 03DI and 03DJ; the represented free-sheaf adjunction.
(blueprint: lem-pc-open-free-restriction-hom)

Proof: Identify morphisms from the represented free sheaf of W with sections on
W, using the sheafification, free/forgetful and Yoneda adjunctions. Naive open
restriction R is left adjoint to direct image G: take the opposite of the
image/preimage adjunction on opens, whisker it by abelian groups, and restrict
it to the full subcategories of sheaves. Its unit on F at the image open W is
F applied to the counit inclusion j(j⁻¹W) ⟶ W. This inclusion is invertible
because W is the image open. Thus postcomposition with the unit is bijective
on morphisms from the free sheaf of W. The adjunction identifies this map with
restriction followed by its Hom equivalence, so restriction is bijective.
Finally transport along Mathlib's natural isomorphism from inverse image to
naive open restriction. The image/preimage identity includes the empty and top
opens without exceptions; the coefficient sheaf F is arbitrary.
-/
theorem H.openFreeSheaf_restrictionHom_bijective {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Function.Bijective (fun a : H.openFreeSheaf j.opensRange ⟶ F =>
      (invImage j).map a) := by
  let hf := j.isOpenEmbedding
  let R := hf.sheafPullback AddCommGrpCat.{u}
  let G := (TopologicalSpace.Opens.map j.base).sheafPushforwardContinuous
    AddCommGrpCat.{u} (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  let adj₀ := hf.isOpenMap.adjunction.op.whiskerLeft AddCommGrpCat.{u}
  let adj : R ⊣ G := adj₀.restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)
  have hu : (adj.unit.app F).hom.app (Opposite.op j.opensRange) =
      F.obj.map ((hf.isOpenMap.adjunction.counit.app j.opensRange).op) := by
    have h := adj₀.map_restrictFullyFaithful_unit_app (L := R) (R := G)
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
      (Iso.refl _) (Iso.refl _) F
    have h' := congrArg (fun f => f.app (Opposite.op j.opensRange)) h
    simpa [adj, adj₀] using h'
  have ht : hf.functor.obj ⊤ = j.opensRange := by
    ext x
    simp [IsOpenMap.functor, Scheme.Hom.opensRange]
  have hi : hf.functor.obj ((TopologicalSpace.Opens.map j.base).obj j.opensRange) =
      j.opensRange := by
    rw [TopologicalSpace.Opens.functor_obj_map_obj hf.isOpenMap, ht, inf_idem]
  have : IsIso (hf.isOpenMap.adjunction.counit.app j.opensRange) := by
    have he : hf.isOpenMap.adjunction.counit.app j.opensRange = eqToHom hi :=
      Subsingleton.elim _ _
    rw [he]
    infer_instance
  have : IsIso ((adj.unit.app F).hom.app (Opposite.op j.opensRange)) := by
    rw [hu]
    infer_instance
  have hb : Function.Bijective (fun a : H.openFreeSheaf j.opensRange ⟶ F =>
      a ≫ adj.unit.app F) := by
    have h := (freeSectionsEquiv j.opensRange (G.obj (R.obj F))).symm.bijective.comp
      ((ConcreteCategory.bijective_of_isIso
        ((adj.unit.app F).hom.app (Opposite.op j.opensRange))).comp
          (freeSectionsEquiv j.opensRange F).bijective)
    convert h using 1
    funext a
    apply (freeSectionsEquiv j.opensRange (G.obj (R.obj F))).injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact freeSectionsEquiv_naturality j.opensRange (adj.unit.app F) a
  have hr : Function.Bijective (fun a : H.openFreeSheaf j.opensRange ⟶ F => R.map a) := by
    have he : (fun a : H.openFreeSheaf j.opensRange ⟶ F => a ≫ adj.unit.app F) =
        (adj.homEquiv _ (R.obj F)) ∘ (fun a => R.map a) := by
      funext a
      exact adj.unit.naturality a
    rw [he] at hb
    exact ((adj.homEquiv _ (R.obj F)).bijective.of_comp_iff' _).mp hb
  let e : invImage j ≅ R := hf.sheafPullbackIso AddCommGrpCat.{u}
  have h := (Iso.homCongr (e.symm.app (H.openFreeSheaf j.opensRange))
    (e.symm.app F)).bijective.comp hr
  convert h using 1
  funext a
  change (invImage j).map a =
    e.hom.app (H.openFreeSheaf j.opensRange) ≫ R.map a ≫ e.inv.app F
  rw [← e.hom.naturality_assoc]
  simp

end AlgebraicGeometry.Scheme.Modules
