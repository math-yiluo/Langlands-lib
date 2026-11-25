/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! Unit calculations on K-flat representatives for derived pullback. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

-- Equality transport and passage to homotopy are independent of the concrete sheaf functors.
private theorem mapHomotopyCategory_leftAdjointCompIso_comp_id
    {K C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (L : K → C ⥤ D) (R : K → D ⥤ C) (adj : ∀ k, L k ⊣ R k)
    [∀ k, (L k).Additive] {I S : D ⥤ D} [I.Additive]
    (ai : I ⊣ S) (ri : S ≅ 𝟭 D) {i j : K} (e : i = j) (d : S ⋙ R j ≅ R i)
    (hd : d ≪≫ eqToIso (congrArg R e) =
      Functor.isoWhiskerRight ri (R j) ≪≫ Functor.leftUnitor (R j))
    {ι : Type*} (c : ComplexShape ι) (H : HomotopyCategory C c) :
    (Functor.mapHomotopyCategoryCompIso
        (Adjunction.leftAdjointCompIso (adj j) ai (adj i) d) c).hom.app H ≫
      (eqToIso (congrArg (fun k ↦ (L k).mapHomotopyCategory c) e)).hom.app H =
    (NatTrans.mapHomotopyCategory (Adjunction.leftAdjointIdIso ai ri).hom c).app
        (((L j).mapHomotopyCategory c).obj H) ≫
      (Functor.mapHomotopyCategoryIdIso D c).hom.app
        (((L j).mapHomotopyCategory c).obj H) := by
  cases e
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hd ⊢
  rw [Adjunction.leftAdjointCompIso_comp_id _ _ _ _ hd]
  rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
  dsimp
  erw [Category.comp_id]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  apply congrArg ((HomotopyCategory.quotient D c).map)
  ext n
  change (Adjunction.leftAdjointIdIso ai ri).hom.app ((L i).obj (P.X n)) ≫ 𝟙 _ = _
  exact Category.comp_id _

private theorem mapHomotopyCategory_leftAdjointCompIso_id_comp
    {K C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (L : K → C ⥤ D) (R : K → D ⥤ C) (adj : ∀ k, L k ⊣ R k)
    [∀ k, (L k).Additive] {I S : C ⥤ C} [I.Additive]
    (ai : I ⊣ S) (ri : S ≅ 𝟭 C) {i j : K} (e : i = j) (d : R j ⋙ S ≅ R i)
    (hd : d ≪≫ eqToIso (congrArg R e) =
      Functor.isoWhiskerLeft (R j) ri ≪≫ Functor.rightUnitor (R j))
    {ι : Type*} (c : ComplexShape ι) (H : HomotopyCategory C c) :
    (Functor.mapHomotopyCategoryCompIso
        (Adjunction.leftAdjointCompIso ai (adj j) (adj i) d) c).hom.app H ≫
      (eqToIso (congrArg (fun k ↦ (L k).mapHomotopyCategory c) e)).hom.app H =
    ((L j).mapHomotopyCategory c).map
      ((NatTrans.mapHomotopyCategory (Adjunction.leftAdjointIdIso ai ri).hom c).app H ≫
        (Functor.mapHomotopyCategoryIdIso C c).hom.app H) := by
  cases e
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] at hd ⊢
  rw [Adjunction.leftAdjointCompIso_id_comp _ _ _ _ hd]
  rw [Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
  erw [Category.comp_id]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  apply congrArg ((HomotopyCategory.quotient D c).map)
  ext n
  change (L i).map ((Adjunction.leftAdjointIdIso ai ri).hom.app (P.X n)) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Tensor composition mates satisfy both unit laws on the homotopy category.
Source: Mathlib.CategoryTheory.Adjunction.CompositionIso,
`Adjunction.leftAdjointCompIso_comp_id` and `Adjunction.leftAdjointCompIso_id_comp`;
Stacks Project, Cohomology, Tag 0D5S, Lemma 20.27.2.
(blueprint: lem-pc-derived-pullback-unit-kflat).
Proof: transport the pinned adjunction of the composite along `id_comp f`
and `comp_id f`, respectively. The pushforward comparison, followed by the same
transport, is the appropriate whiskering of `pushforwardId`: this is checked
on sections, where all comparison maps are identities. Apply the two Mathlib
left-adjoint composition unit laws to these equalities. Map the resulting
natural transformations termwise to complexes and then to the homotopy category.
The complex comparison maps are termwise identities and the quotient functor
preserves composition, giving exactly the two displayed identities. This argument
uses no derived functor, K-flatness, or resolution, and also applies to the zero
complex and to an identity morphism. -/
private theorem tensorPullback_homotopy_unit
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
    {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    (H : HomotopyCategory (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
      (ComplexShape.up ℤ)) :
    ((Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction ((𝟙 X) ≫ f)))
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).comp
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X))))).symm
          (Scheme.Modules.pushforwardComp (𝟙 X) f).symm)
        (ComplexShape.up ℤ)).hom.app H ≫
      (eqToIso (congrArg (fun k : X ⟶ Y ↦
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (ComplexShape.up ℤ))
        (Category.id_comp f))).hom.app H =
      (NatTrans.mapHomotopyCategory
          (Adjunction.leftAdjointIdIso
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
            (Scheme.Modules.pushforwardId X)).hom (ComplexShape.up ℤ)).app
          (((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj H) ≫
        (Functor.mapHomotopyCategoryIdIso
          (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
          (ComplexShape.up ℤ)).hom.app (((Scheme.Modules.tensorPullback f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj H)) ∧
    ((Functor.mapHomotopyCategoryCompIso
        ((conjugateIsoEquiv
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ (𝟙 Y))))
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 Y))).comp
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
          (Scheme.Modules.pushforwardComp f (𝟙 Y)).symm)
        (ComplexShape.up ℤ)).hom.app H ≫
      (eqToIso (congrArg (fun k : X ⟶ Y ↦
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (ComplexShape.up ℤ))
        (Category.comp_id f))).hom.app H =
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory
          (Adjunction.leftAdjointIdIso
            (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 Y)))
            (Scheme.Modules.pushforwardId Y)).hom (ComplexShape.up ℤ)).app H ≫
        (Functor.mapHomotopyCategoryIdIso
          (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
          (ComplexShape.up ℤ)).hom.app H)) := by
  let adj {X Y : Scheme.{u₁}} (k : X ⟶ Y) :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  constructor
  · exact mapHomotopyCategory_leftAdjointCompIso_comp_id
      (fun k : X ⟶ Y ↦ Scheme.Modules.tensorPullback k)
      (fun k : X ⟶ Y ↦ Scheme.Modules.pushforward k) adj
      (adj (𝟙 X)) (Scheme.Modules.pushforwardId X) (Category.id_comp f)
      (Scheme.Modules.pushforwardComp (𝟙 X) f) (by
        ext M U
        rfl) (ComplexShape.up ℤ) H
  · exact mapHomotopyCategory_leftAdjointCompIso_id_comp
      (fun k : X ⟶ Y ↦ Scheme.Modules.tensorPullback k)
      (fun k : X ⟶ Y ↦ Scheme.Modules.pushforward k) adj
      (adj (𝟙 Y)) (Scheme.Modules.pushforwardId Y) (Category.comp_id f)
      (Scheme.Modules.pushforwardComp f (𝟙 Y)) (by
        ext M U
        rfl) (ComplexShape.up ℤ) H


/-- The two unit comparisons agree on a K-flat representative, for identity
isomorphisms normalized by the tensor identity mate.
Source: Stacks Project, Cohomology, Tag 0D5S, Lemma 20.27.2;
Mathlib `Adjunction.leftAdjointCompIso_comp_id` and
`Adjunction.leftAdjointCompIso_id_comp`.
(blueprint: lem-pc-derived-pullback-unit-kflat).
Proof: write H for the homotopy image of P. Apply hc to the hom of each
composition comparison and use leftDerived_fac_app at H. The resulting expression
is the two successive counits followed by the homotopy image of the tensor
composition mate. For c(id_X,f), naturality of the counit of id_X moves the
counit of f past it. Substitute hi X evaluated at the tensor pullback of H;
this replaces the identity counit followed by the tensor identity mate by
Qh applied to i X. For c(f,id_Y), substitute hi Y at H and use naturality
of the counit of f. The underived identities are respectively
leftAdjointCompIso_comp_id and leftAdjointCompIso_id_comp, applied to the
pinned adjunctions and pushforward identity laws. When rewriting id_comp or
comp_id, transport the pinned adjunctions as well; conjugateIsoEquiv is natural
under that transport. The homotopy images and Qh preserve these equalities.
The two expressions now agree after postcomposition with the counit of f
at H. This counit is invertible by hK f P hP, so cancel it. Functor unitors
have identity components, giving the two displayed component equalities.
No nonempty, flat-morphism, or boundedness hypothesis is used: the argument also
applies to zero complexes, empty schemes, and f an identity. -/
theorem derivedPullbackComposition_unit_kflat
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hK : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y)
      (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ),
      CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
        IsIso ((ε f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
    (hc :∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (c f g).hom =
          (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
    (i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _)
    (hi : ∀ X : Scheme.{u₁},
        Functor.whiskerLeft (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) (i X).hom ≫
            (Functor.rightUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom =
          ε (𝟙 X) ≫
            Functor.whiskerRight
              (NatTrans.mapHomotopyCategory
                (Adjunction.leftAdjointIdIso
                  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
                  (Scheme.Modules.pushforwardId X)).hom (ComplexShape.up ℤ))
              (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            Functor.whiskerRight
              (Functor.mapHomotopyCategoryIdIso
                (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
                (ComplexShape.up ℤ)).hom (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            (Functor.leftUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom)
    {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    ((c (𝟙 X) f ≪≫
        eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.id_comp f))).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
      Functor.rightUnitor (derivedPullback f)).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
    ((c f (𝟙 Y) ≪≫
        eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.comp_id f))).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
      Functor.leftUnitor (derivedPullback f)).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := by
  let H := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P
  have := hK f P hP
  have transport (k l : X ⟶ Y) (e : k = l) :
      (eqToIso (congrArg (fun m ↦ derivedPullback m) e)).hom.app
          (DerivedCategory.Qh.obj H) ≫ (ε l).app H =
        (ε k).app H ≫ DerivedCategory.Qh.map
          ((eqToIso (congrArg (fun m ↦
            (Scheme.Modules.tensorPullback m).mapHomotopyCategory
              (ComplexShape.up ℤ)) e)).hom.app H) := by
    subst l
    simp
  obtain ⟨huX, huY⟩ := tensorPullback_homotopy_unit a f H
  have hiX := congrArg (fun t ↦ t.app
    (((Scheme.Modules.tensorPullback f).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj H)) (hi X)
  have hiY := congrArg (fun t ↦ t.app H) (hi Y)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj] at hiX hiY
  simp only [Category.comp_id] at hiX hiY
  constructor
  · apply (cancel_mono ((ε f).app H)).1
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [transport _ _ (Category.id_comp f), hc, ← Category.assoc,
      Functor.leftDerived_fac_app]
    simp only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.assoc]
    rw [← Functor.map_comp, huX, Functor.map_comp]
    rw [← hiX]
    simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app]
    dsimp
    have hnX := (i X).hom.naturality ((ε f).app H)
    dsimp at hnX
    simp only [Category.id_comp]
    convert hnX using 1
  · apply (cancel_mono ((ε f).app H)).1
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [transport _ _ (Category.comp_id f), hc, ← Category.assoc,
      Functor.leftDerived_fac_app]
    simp only [NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.assoc]
    rw [← Functor.map_comp, huY]
    have hn := (ε f).naturality
      ((NatTrans.mapHomotopyCategory
        (Adjunction.leftAdjointIdIso
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 Y)))
          (Scheme.Modules.pushforwardId Y)).hom (ComplexShape.up ℤ)).app H ≫
        (Functor.mapHomotopyCategoryIdIso
          (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))
          (ComplexShape.up ℤ)).hom.app H)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← Functor.map_comp] at hiY
    rw [← hn, ← Category.assoc, ← (derivedPullback f).map_comp, ← hiY]
    simp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app]
    dsimp
    simp only [Category.id_comp]
    rfl

end AlgebraicGeometry
