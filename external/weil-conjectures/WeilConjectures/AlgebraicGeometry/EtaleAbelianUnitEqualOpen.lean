/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpen
import WeilConjectures.AlgebraicGeometry.EtaleSetCartesianUnitEquality
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-! # The agreement open of two abelian étale sheaf sections

Source: Stacks Project, Étale Cohomology Tag 09XM, with Tags 03Q1 and 03S2.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Etale

private theorem isIso_abelian_forget_comparison
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (AddCommGrpCat.{u + 1})) :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
      (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).homEquiv
      ((sheafCompose Y.smallEtaleTopology (forget (AddCommGrpCat.{u + 1}))).obj G)
      ((sheafCompose X.smallEtaleTopology (forget (AddCommGrpCat.{u + 1}))).obj
        ((g)^*[AddCommGrpCat.{u + 1}].obj G))).symm
        ((sheafCompose Y.smallEtaleTopology (forget (AddCommGrpCat.{u + 1}))).map
          ((upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g).unit.app G))) := by
  let U := forget (AddCommGrpCat.{u + 1})
  let B := MorphismProperty.Over.pullback @Etale ⊤ g
  let L := B.op
  have : X.smallEtaleTopology.PreservesSheafification U := inferInstance
  have h : U.PreservesLeftKanExtensions L := by
    intro F
    have : U.PreservesPointwiseLeftKanExtension F L := by
      intro c
      have : IsFiltered (CostructuredArrow L c) :=
        IsFiltered.of_equivalence (structuredArrowOpEquivalence B c.unop)
      have : PreservesFilteredColimitsOfSize.{u, u + 1} U :=
        preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} U
      exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit U F L c
    exact Functor.preservesPointwiseLKEOfHasPointwiseAndPreservesPointwise U F L
  let e := U.lanCompIsoOfPreserves L
  let e' := sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction _ _) (sheafificationAdjunction _ _)
  let q := (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
      ((e.app G.obj).inv) ≫ e'.hom.app (L.lan.obj G.obj)
  have : IsIso q := inferInstance
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
    (Type (u + 1)) (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
    (X.smallGrothendieckTopology (Q := @Etale) @Etale)
  let F := (sheafCompose Y.smallEtaleTopology U).obj G
  let H := (sheafCompose X.smallEtaleTopology U).obj ((g)^*[AddCommGrpCat.{u + 1}].obj G)
  have hq : (adj.homEquiv F H).symm
      ((sheafCompose Y.smallEtaleTopology U).map
        ((upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g).unit.app G)) = q := by
    apply (adj.homEquiv F H).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    apply (sheafToPresheaf _ _).map_injective
    change whiskerRight
      ((upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1}) g).unit.app G).hom U =
      (adj.unit.app F).hom ≫ B.op.whiskerLeft q.hom
    rw [show (adj.unit.app F).hom = B.op.lanUnit.app F.obj ≫ B.op.whiskerLeft
        (toSheafify (D := Type (u + 1)) X.smallEtaleTopology
          (B.op.leftKanExtension F.obj)) from by
      change (sheafToPresheaf Y.smallEtaleTopology (Type (u + 1))).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
          (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
          (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app F) = _
      dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Functor.lan, ObjectProperty.ι_obj, Functor.id_obj,
        Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
        sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map,
        Iso.refl_hom, NatTrans.id_app, Functor.comp_map,
        ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, Category.assoc]
      rfl]
    change whiskerRight
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
        (AddCommGrpCat.{u + 1}) (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
        (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom U = _
    rw [show ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
      (AddCommGrpCat.{u + 1}) (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
      (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G).hom =
        B.op.lanUnit.app G.obj ≫ B.op.whiskerLeft
        (toSheafify (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology
          (B.op.leftKanExtension G.obj)) from by
      change (sheafToPresheaf Y.smallEtaleTopology (AddCommGrpCat.{u + 1})).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ g) (AddCommGrpCat.{u + 1})
          (Y.smallGrothendieckTopology (Q := @Etale) @Etale)
          (X.smallGrothendieckTopology (Q := @Etale) @Etale)).unit.app G) = _
      dsimp only [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Functor.lan, ObjectProperty.ι_obj, Functor.id_obj,
        Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
        sheafificationAdjunction_unit_app, Functor.whiskeringLeft_obj_map,
        Iso.refl_hom, NatTrans.id_app, Functor.comp_map,
        ObjectProperty.ι_map, ObjectProperty.FullSubcategory.id_hom, Category.assoc]
      rfl]
    simp only [whiskerRight_comp, Category.assoc]
    dsimp only [q, ObjectProperty.FullSubcategory.comp_hom]
    rw [← B.op.whiskerLeft_comp]
    have hn := (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).unit.naturality
      ((e.app G.obj).inv)
    have hs := sheafComposeNatTrans_fac X.smallEtaleTopology U
      (sheafificationAdjunction _ _) (sheafificationAdjunction _ _) (L.lan.obj G.obj)
    change (e.app G.obj).inv ≫ toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) =
      toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map (e.app G.obj).inv).hom
      at hn
    change whiskerRight (L.leftKanExtensionUnit G.obj) U ≫
      L.whiskerLeft (whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U) =
      L.leftKanExtensionUnit (G.obj ⋙ U) ≫ L.whiskerLeft
        (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U)) ≫
          ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map (e.app G.obj).inv).hom ≫
          (e'.hom.app (L.lan.obj G.obj)).hom)
    change toSheafify X.smallEtaleTopology (L.lan.obj G.obj ⋙ U) ≫
      (e'.hom.app (L.lan.obj G.obj)).hom =
      whiskerRight (toSheafify X.smallEtaleTopology (L.lan.obj G.obj)) U at hs
    rw [← Category.assoc (toSheafify X.smallEtaleTopology (L.lan.obj (G.obj ⋙ U))),
      ← hn, Category.assoc, hs]
    rw [B.op.whiskerLeft_comp]
    rw [← Category.assoc]
    change _ = (L.leftKanExtensionUnit (G.obj ⋙ U) ≫
      L.whiskerLeft (U.leftKanExtensionCompIsoOfPreserves G.obj L).inv) ≫ _
    rw [Functor.leftKanExtensionCompIsoOfPreserves_inv_fac]
    rfl
  rw [hq]
  infer_instance


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Equality of inverse-image unit sections is characterized by the inverse image
of an open in the original étale object being the whole base-changed object.
Source: Stacks Project, Étale Cohomology Tag 09XM (agreement open),
Tag 03Q1 (inverse image on geometric stalks), and Tag 03S2 (étale restriction).
(blueprint: lem-weil-pbc-etale-abelian-unit-equal-open).

Proof: Forget the abelian operations and use the set-valued agreement-open
existence theorem to obtain W. For each f, the canonical comparison from the
set pullback to the underlying abelian pullback is an isomorphism: the forgetful
functor preserves the filtered colimits computing left Kan extension, and it
preserves sheafification. Compose their canonical comparisons. The Kan-extension
and sheafification unit equations identify this composite with the adjoint
transpose of the forgotten abelian unit. Evaluating the adjunction equation
shows that this isomorphism sends the set unit images to the abelian unit images,
so these images agree exactly when the set unit images agree.
Apply the cartesian-unit equality criterion to A = U ×[S] X with the identity
isomorphism and p its first projection. It identifies equality of the set unit
images with equality after arbitrary restriction along p. The defining property
of W identifies the latter with factorization of p through W. Such a factorization
implies p inverse-image W = top by evaluation on points; conversely that equality
gives the factorization by the open-immersion lifting property.
For empty U the open and its pullbacks are empty and all sections agree. For
s = t the agreement open is top. No compactness, limit, or directedness is used. -/
theorem etale_abelian_unit_equal_open
    (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : S.Etale) (s t : F.obj.obj (op U)) :
    ∃ W : U.left.Opens, ∀ (X : Scheme.{u}) (f : X ⟶ S),
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app
          (op U) s =
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app
          (op U) t) ↔
      pullback.fst U.hom f ⁻¹ᵁ W = ⊤ := by
  classical
  let F₀ := (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj F
  obtain ⟨W, hW, _⟩ := existsUnique_etaleSections_equal_open S F₀ U s t
  refine ⟨W, ?_⟩
  intro X f
  let B := MorphismProperty.Over.pullback @Etale ⊤ f
  let A := B.obj U
  let p := pullback.fst U.hom f
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous B
    (Type (u + 1)) (S.smallGrothendieckTopology @Etale)
    (X.smallGrothendieckTopology @Etale)
  let H := (sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj
    ((upperStar AddCommGrpCat.{u + 1} f).obj F)
  let m := (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F)
  let q := (adj.homEquiv F₀ H).symm m
  have : IsIso q := isIso_abelian_forget_comparison f F
  let χ := q.hom.app (op A)
  let η := (adj.unit.app F₀).hom.app (op U)
  let ηab := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app
    (op U)
  have hfac : adj.unit.app F₀ ≫ (B.sheafPushforwardContinuous (Type (u + 1))
      (S.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)).map q = m := by
    exact (adj.homEquiv_unit F₀ H q).symm.trans
      ((adj.homEquiv F₀ H).apply_symm_apply m)
  have hvalue (x : F.obj.obj (op U)) : χ (η x) = ηab x := by
    have hv := NatTrans.congr_app (congrArg (fun a ↦ a.hom) hfac) (op U)
    change η ≫ χ = (forget AddCommGrpCat.{u + 1}).map ηab at hv
    exact congrArg (fun k ↦ k x) hv
  have heq : ηab s = ηab t ↔ η s = η t := by
    constructor
    · intro h
      apply CategoryTheory.injective_of_mono χ
      rw [hvalue s, hvalue t, h]
    · intro h
      rw [← hvalue s, ← hvalue t, h]
  have hunit := etaleSetCartesianUnit_eq_iff f F₀ U A (Iso.refl A) p
    (Category.id_comp p) s t
  have hopen : (∃ b : A.left ⟶ W.toScheme, b ≫ W.ι = p) ↔ p ⁻¹ᵁ W = ⊤ := by
    constructor
    · rintro ⟨b, hb⟩
      apply top_unique
      intro x _
      change p x ∈ W
      have hx := congrArg (fun a : A.left ⟶ U.left ↦ a x) hb
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at hx
      exact hx ▸ (b x).property
    · intro hall
      refine ⟨IsOpenImmersion.lift W.ι p ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro x ⟨y, rfl⟩
      have hy : y ∈ p ⁻¹ᵁ W := by rw [hall]; trivial
      exact hy
  exact heq.trans (hunit.trans ((hW A.left p).symm.trans hopen))

end AlgebraicGeometry.Etale
