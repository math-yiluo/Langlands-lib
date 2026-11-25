/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction

/-! # Reduction of a specified morphism of principal Milnor triangles

Source: Stacks Project, algebraization.tex, principal derived-completion argument;
proetale.tex, Tag 099M, lemma-naive-completion.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory Opposite
namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

private theorem isIso_map_of_milnor
    {A B : Type*} [Category A] [Category B]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    [HasZeroObject B] [HasShift B ℤ] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (TM : A ⥤ B) [TM.Additive] [TM.CommShift ℤ] [TM.IsTriangulated]
    {F G : ℕᵒᵖ ⥤ A} {X Y : A} (u : X ⟶ Y)
    (PK : Fan fun n : ℕ ↦ F.obj (op n)) (hPK : IsLimit PK)
    (PG : Fan fun n : ℕ ↦ G.obj (op n)) (hPG : IsLimit PG)
    (cX : X ⟶ PK.pt) (δK : PK.pt ⟶ X⟦(1 : ℤ)⟧)
    (cY : Y ⟶ PG.pt) (δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧)
    (hTK : Triangle.mk cX (𝟙 PK.pt - towerShift hPK) δK ∈ distTriang A)
    (hTY : Triangle.mk cY (𝟙 PG.pt - towerShift hPG) δY ∈ distTriang A)
    (a : F ⟶ G)
    (hu₁ : cX ≫ productTowerMap (PF := PK) hPG a = u ≫ cY)
    (hu₃ : δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG a ≫ δY)
    (hPKM : IsLimit (Fan.mk (TM.obj PK.pt) (fun n ↦ TM.map (PK.proj n))))
    (hPGM : IsLimit (Fan.mk (TM.obj PG.pt) (fun n ↦ TM.map (PG.proj n))))
    (b : ∀ n : ℕ, (G ⋙ TM).obj (op (n + 1)) ⟶ (F ⋙ TM).obj (op n))
    (hb₁ : ∀ n, b n ≫ (Functor.whiskerRight a TM).app (op n) =
      (G ⋙ TM).map (homOfLE n.le_succ).op)
    (hb₂ : ∀ n, (Functor.whiskerRight a TM).app (op (n + 1)) ≫ b n =
      (F ⋙ TM).map (homOfLE n.le_succ).op) : IsIso (TM.map u) := by
  let PKM : Fan fun n : ℕ ↦ (F ⋙ TM).obj (op n) :=
    Fan.mk (TM.obj PK.pt) fun n ↦ TM.map (PK.proj n)
  let PGM : Fan fun n : ℕ ↦ (G ⋙ TM).obj (op n) :=
    Fan.mk (TM.obj PG.pt) fun n ↦ TM.map (PG.proj n)
  let m := productTowerMap (PF := PK) hPG a
  have htK : TM.map (towerShift (F := F) hPK) = towerShift (F := F ⋙ TM) hPKM :=
    Fan.IsLimit.hom_ext hPKM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have htG : TM.map (towerShift (F := G) hPG) = towerShift (F := G ⋙ TM) hPGM :=
    Fan.IsLimit.hom_ext hPGM _ _ fun n ↦ by
      change TM.map _ ≫ TM.map _ = _
      rw [towerShift_proj, ← TM.map_comp, towerShift_proj, TM.map_comp]
      rfl
  have hTKM : Triangle.mk (TM.map cX) (𝟙 _ - towerShift (F := F ⋙ TM) hPKM)
      (TM.map δK ≫ (TM.commShiftIso (1 : ℤ)).hom.app X) ∈ distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hTK) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp]
          change _ = TM.map (𝟙 PK.pt - towerShift (F := F) hPK)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, htK]
          rfl)
        (by simp))
  have hTYM : Triangle.mk (TM.map cY) (𝟙 _ - towerShift (F := G ⋙ TM) hPGM)
      (TM.map δY ≫ (TM.commShiftIso (1 : ℤ)).hom.app Y) ∈ distTriang _ :=
    isomorphic_distinguished _ (TM.map_distinguished _ hTY) _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
        (by
          simp only [Triangle.mk_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp]
          change _ = TM.map (𝟙 PG.pt - towerShift (F := G) hPG)
          rw [Functor.map_sub, CategoryTheory.Functor.map_id, htG]
          rfl)
        (by simp))
  let aM := Functor.whiskerRight a TM
  have hm : productTowerMap (PF := PKM) hPGM aM = TM.map m :=
    Fan.IsLimit.hom_ext hPGM _ _ fun n ↦ by
      rw [productTowerMap_proj]
      change _ = TM.map _ ≫ TM.map _
      rw [← TM.map_comp, productTowerMap_proj, TM.map_comp]
      rfl
  exact isIso_of_proIso hPKM hPGM hTKM hTYM aM b hb₁ hb₂
    (TM.map u)
    (by
      rw [hm]
      change TM.map cX ≫ TM.map m = TM.map u ≫ TM.map cY
      rw [← TM.map_comp, ← TM.map_comp]
      exact congrArg TM.map hu₁)
    (by
      rw [hm, Category.assoc, ← TM.commShiftIso_hom_naturality,
        ← TM.map_comp_assoc, hu₃, TM.map_comp_assoc])

/-- A map from the constant Milnor triangle to the principal quotient Milnor triangle
becomes invertible after reduction by the principal generator, provided both squares
for the map are specified, including the shifted boundary square.

Source: Stacks Project, algebraization.tex, principal derived-completion Koszul proof;
proetale.tex, Tag 099M, lemma-naive-completion
(blueprint: lem-sfb-principal-milnor-augmentation-reduction).
Proof: tensor both limiting product fans by the first quotient, using the source
principal product comparison. Product extensionality identifies both shifted tower
endomorphisms and the product map with their images under this tensor functor. Its
triangulated structure therefore gives the two reduced Milnor triangles. The source
successor lifts for the twice-reduced principal tower satisfy both pro-isomorphism
identities. Apply the source Milnor pro-isomorphism criterion to the specified map;
functoriality gives its first square, and naturality of the tensor shift comparison
gives its last square. Finally the coefficient isomorphism R/I^1 = R/I gives an
isomorphism between this tensor functor and reductionModIdeal. Naturality transports
invertibility to exactly the reduced original map. -/
theorem isIso_reductionModIdeal_of_principalMilnorMorphism
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    {I : Ideal R} {r : R} (hr : r ∈ nonZeroDivisors R) (hI : I = Ideal.span {r})
    (K Y : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (u : K ⟶ Y)
    (PK : Fan fun _ : ℕ ↦ K) (hPK : IsLimit PK)
    (PG : Fan fun n : ℕ ↦ (DerivedCategory.derivedCompletionDiagram J I K).obj (op n))
    (hPG : IsLimit PG)
    (δK : PK.pt ⟶ K⟦(1 : ℤ)⟧) (cY : Y ⟶ PG.pt) (δY : PG.pt ⟶ Y⟦(1 : ℤ)⟧)
    (hTK : Triangle.mk (Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K))
      (𝟙 PK.pt - towerShift (F := (Functor.const ℕᵒᵖ).obj K) hPK) δK ∈
        distTriang (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))))
    (hTY : Triangle.mk cY
      (𝟙 PG.pt - towerShift (F := DerivedCategory.derivedCompletionDiagram J I K) hPG)
      δY ∈ distTriang (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))))
    (hu₁ : Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K) ≫ productTowerMap (PF := PK) hPG
      (DerivedCategory.derivedCompletionCone J I K).π = u ≫ cY)
    (hu₃ : δK ≫ u⟦(1 : ℤ)⟧' = productTowerMap (PF := PK) hPG
      (DerivedCategory.derivedCompletionCone J I K).π ≫ δY) :
    IsIso ((DerivedCategory.reductionModIdeal J I).map u) := by
  classical
  let F := (Functor.const ℕᵒᵖ).obj K
  let G := DerivedCategory.derivedCompletionDiagram J I K
  let a : F ⟶ G := (DerivedCategory.derivedCompletionCone J I K).π
  let cK := Fan.IsLimit.lift hPK (fun _ ↦ 𝟙 K)
  let M := (DerivedCategory.quotPowFunctor J I).obj (op 1)
  let TM := (curriedTensor (DerivedCategory
    (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj M
  let FM := F ⋙ TM
  let GM := G ⋙ TM
  let PKM : Fan fun n : ℕ ↦ FM.obj (op n) :=
    Fan.mk (TM.obj PK.pt) fun n ↦ TM.map (PK.proj n)
  let PGM : Fan fun n : ℕ ↦ GM.obj (op n) :=
    Fan.mk (TM.obj PG.pt) fun n ↦ TM.map (PG.proj n)
  have hPKM : IsLimit PKM := DerivedCategory.isLimit_fan_whiskerRight_quot hr hI hPK
  have hPGM : IsLimit PGM := DerivedCategory.isLimit_fan_whiskerRight_quot hr hI hPG
  have hb := DerivedCategory.exists_lift_whiskerRight_derivedCompletionCone hr hI K
  choose b hb₁ hb₂ using hb
  have hred : IsIso (TM.map u) := isIso_map_of_milnor TM u PK hPK PG hPG
    cK δK cY δY hTK hTY a hu₁ hu₃ hPKM hPGM b hb₁ hb₂
  let d : M ≅ (DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf J (ModuleCat.{u + 1} R)).obj
        (ModuleCat.of R (R ⧸ I))) :=
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf J (ModuleCat.{u + 1} R)).mapIso
        ((Submodule.quotEquivOfEq _ _ (pow_one I)).toModuleIso))
  let θ : TM ≅ DerivedCategory.reductionModIdeal J I :=
    (curriedTensor (DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} R)))).flip.mapIso d
  have hnat := θ.hom.naturality u
  have heq : (DerivedCategory.reductionModIdeal J I).map u =
      θ.inv.app K ≫ TM.map u ≫ θ.hom.app Y := by
    apply (cancel_epi (θ.hom.app K)).1
    rw [Iso.hom_inv_id_app_assoc]
    exact hnat.symm
  rw [heq]
  infer_instance

end DerivedCategory
