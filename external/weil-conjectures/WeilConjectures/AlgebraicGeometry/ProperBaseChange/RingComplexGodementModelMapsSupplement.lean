/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
public import WeilConjectures.AlgebraicGeometry.RingComplexCechData
public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
public import WeilConjectures.CategoryTheory.SimplexPresentationFaithful
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementRelations
public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialInput
public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelPairing
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingForModels
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairings
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonicalCollapse
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonical
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementBetaExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinatesExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorStalkPairingExists
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorMapOfPairingExists
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairingsFromBeta
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementStalkContraction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Algebra.Homology.ModuleStalkExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Products
import all WeilConjectures.AlgebraicGeometry.Module.ModuleCupGodementFMapModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Module.ModuleCupCosimplicialFMapSummandsSupplement

/-! # Strict maps between the prescribed Godement models

## References

* Stacks Project, Tag 0FKS, the coordinate product-of-stalks construction
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial
namespace AlgebraicGeometry
open Scheme.Modules
noncomputable section

private theorem model_spec (X : Scheme.{u}) :
    ModuleCupGodementModel X (SheafOfModules.unit X.ringCatSheaf)
      (ringComplexGodementModel X) (ringComplexGodementUnit X) :=
  (moduleCup_godement_models_exist X
    (SheafOfModules.unit X.ringCatSheaf)).choose_spec.choose_spec.1

private theorem model_codeg (X : Scheme.{u}) :
    ModuleCupGodementCodegeneracies X (SheafOfModules.unit X.ringCatSheaf)
      (ringComplexGodementModel X) :=
  (moduleCup_godement_models_exist X
    (SheafOfModules.unit X.ringCatSheaf)).choose_spec.choose_spec.2

private theorem stalk_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : X.Modules} {G : Y.Modules} {H : Z.Modules}
    (q : F ⟶ (pushforward f).obj G) (r : G ⟶ (pushforward g).obj H)
    (z : Z) (s : F.presheaf.stalk ((g ≫ f) z)) :
    FMap.stalk (g ≫ f) (q ≫ (pushforward f).map r ≫ (pushforwardComp g f).hom.app H) z s =
      FMap.stalk g r z (FMap.stalk f q (g z) s) := by
  obtain ⟨U, hz, s, rfl⟩ := F.presheaf.exists_germ_eq s
  erw [FMap.stalk_germ, FMap.stalk_germ, FMap.stalk_germ]
  rfl

private theorem lift_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : X.Modules} {G : Y.Modules} {H : Z.Modules}
    (q : F ⟶ (pushforward f).obj G) (r : G ⟶ (pushforward g).obj H) :
    FMap.lift (g ≫ f) (q ≫ (pushforward f).map r ≫ (pushforwardComp g f).hom.app H) =
      FMap.lift f q ≫ (pushforward f).map (FMap.lift g r) ≫
        (pushforwardComp g f).hom.app (moduleCup_godementObject Z H) := by
  apply FMap.target_ext (g ≫ f) H
  intro z
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hz
  change (FMap.proj Z H z).app ((g ≫ f) ⁻¹ᵁ U)
      ((FMap.lift (g ≫ f) _).app U s) ⟨hz⟩ =
    (FMap.proj Z H z).app (g ⁻¹ᵁ (f ⁻¹ᵁ U))
      ((FMap.lift g r).app (f ⁻¹ᵁ U) ((FMap.lift f q).app U s)) ⟨hz⟩
  erw [FMap.lift_apply, FMap.lift_apply, FMap.lift_apply, stalk_comp]
  rfl

private theorem stalk_id (X : Scheme.{u}) (F : X.Modules) (x : X)
    (s : F.presheaf.stalk x) :
    FMap.stalk (𝟙 X) ((pushforwardId X).inv.app F) x s = s := by
  obtain ⟨U, hx, s, rfl⟩ := F.presheaf.exists_germ_eq s
  erw [FMap.stalk_germ]
  rfl

private theorem lift_id (X : Scheme.{u}) (F : X.Modules) :
    FMap.lift (𝟙 X) ((pushforwardId X).inv.app F) =
      (pushforwardId X).inv.app (moduleCup_godementObject X F) := by
  apply FMap.target_ext (𝟙 X) F
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  have hh := FMap.lift_apply (𝟙 X) ((pushforwardId X).inv.app F) x U hx s
  erw [stalk_id] at hh
  exact hh

private theorem iterate_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    {F : X.Modules} {G : Y.Modules} {H : Z.Modules}
    (q : F ⟶ (pushforward f).obj G) (r : G ⟶ (pushforward g).obj H) (n : ℕ) :
    FMap.iterate (g ≫ f)
        (q ≫ (pushforward f).map r ≫ (pushforwardComp g f).hom.app H) n =
      FMap.iterate f q n ≫ (pushforward f).map (FMap.iterate g r n) ≫
        (pushforwardComp g f).hom.app (moduleCup_godementIterate Z H n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change FMap.lift (g ≫ f) _ = FMap.lift f _ ≫
      (pushforward f).map (FMap.lift g _) ≫ _
    rw [ih, lift_comp]
    rfl

private theorem iterate_id (X : Scheme.{u}) (F : X.Modules) (n : ℕ) :
    FMap.iterate (𝟙 X) ((pushforwardId X).inv.app F) n =
      (pushforwardId X).inv.app (moduleCup_godementIterate X F n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change FMap.lift (𝟙 X) _ = _
    rw [ih, lift_id]
    rfl

private def cosmap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) :
    ringComplexGodementModel X ⟶ ringComplexGodementModel Y ⋙ pushforward f :=
  (FMap.modelMap f q (ringComplexGodementModel X) (ringComplexGodementModel Y)
    (ringComplexGodementUnit X) (ringComplexGodementUnit Y)
    (model_spec X) (model_spec Y) (model_codeg X) (model_codeg Y)).choose

private theorem cosmap_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) (n : SimplexCategory) :
    (cosmap f q).app n = eqToHom ((model_spec X).choose n.len) ≫
      FMap.iterate f q (n.len + 1) ≫
        (pushforward f).map (eqToHom ((model_spec Y).choose n.len).symm) :=
  (FMap.modelMap f q (ringComplexGodementModel X) (ringComplexGodementModel Y)
    (ringComplexGodementUnit X) (ringComplexGodementUnit Y)
    (model_spec X) (model_spec Y) (model_codeg X) (model_codeg Y)).choose_spec n

private theorem cosmap_id (X : Scheme.{u}) (n : SimplexCategory) :
    (cosmap (𝟙 X) ((pushforwardId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf))).app n =
        (pushforwardId X).inv.app ((ringComplexGodementModel X).obj n) := by
  rw [cosmap_app, iterate_id]
  rw [← (pushforwardId X).inv.naturality]
  simp only [Functor.id_map, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

private theorem cosmap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
    (r : SheafOfModules.unit Y.ringCatSheaf ⟶
      (pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) (n : SimplexCategory) :
    (cosmap (g ≫ f)
      (q ≫ (pushforward f).map r ≫
        (pushforwardComp g f).hom.app (SheafOfModules.unit Z.ringCatSheaf))).app n =
      (cosmap f q).app n ≫ (pushforward f).map ((cosmap g r).app n) ≫
        (pushforwardComp g f).hom.app ((ringComplexGodementModel Z).obj n) := by
  rw [cosmap_app, cosmap_app, cosmap_app, iterate_comp]
  simp only [Functor.map_comp, Category.assoc]
  have hc := (pushforwardComp g f).hom.naturality
    (eqToHom ((model_spec Z).choose n.len).symm)
  dsimp only [Functor.comp_map] at hc
  simp only [← Functor.map_comp_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [hc]

private def resmap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) :
    ringComplexGodementResolution X ⟶
      ((pushforward f).mapHomologicalComplex (.up ℤ)).obj (ringComplexGodementResolution Y) :=
  crossMap X Y f (ringComplexGodementModel X) (ringComplexGodementModel Y) (cosmap f q)

private theorem resmap_nat {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) (n : ℕ) :
    (resmap f q).f (n : ℤ) =
      (((alternatingCofaceMapComplex X.Modules).obj (ringComplexGodementModel X)).extendXIso
        ComplexShape.embeddingUpNat (i := n) rfl).hom ≫ (cosmap f q).app ⦋n⦌ ≫
      (pushforward f).map
        ((((alternatingCofaceMapComplex Y.Modules).obj (ringComplexGodementModel Y)).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl).inv) := by
  exact crossComponent_nat X Y f _ _ _ n

private theorem resmap_aug {X Y : Scheme.{u}} (f : Y ⟶ X)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) :
    (ringComplexGodementUnit X).f 0 ≫ (resmap f q).f 0 =
      q ≫ (pushforward f).map ((ringComplexGodementUnit Y).f 0) := by
  have ha := FMap.modelMap_augmentation f q
    (ringComplexGodementModel X) (ringComplexGodementModel Y)
    (ringComplexGodementUnit X) (ringComplexGodementUnit Y)
    (model_spec X) (model_spec Y) (cosmap f q) (cosmap_app f q)
  erw [resmap_nat f q 0]
  dsimp only [moduleCup_cosimplicialZeroIso] at ha
  have hh := congrArg (fun z ↦ z ≫ (pushforward f).map
    ((((alternatingCofaceMapComplex Y.Modules).obj (ringComplexGodementModel Y)).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).inv)) ha
  have hi :
      (pushforward f).map
          ((((alternatingCofaceMapComplex Y.Modules).obj (ringComplexGodementModel Y)).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫
        (pushforward f).map
          ((((alternatingCofaceMapComplex Y.Modules).obj (ringComplexGodementModel Y)).extendXIso
            ComplexShape.embeddingUpNat (i := 0) rfl).inv) = 𝟙 _ := by
    erw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  simp only [Category.assoc, Functor.map_comp] at hh
  erw [hi, Category.comp_id] at hh
  exact hh

private theorem resmap_id (X : Scheme.{u}) (n : ℤ) :
    (resmap (𝟙 X) ((pushforwardId X).inv.app
      (SheafOfModules.unit X.ringCatSheaf))).f n =
        (pushforwardId X).inv.app ((ringComplexGodementResolution X).X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [resmap_nat, cosmap_id]
    rw [← (pushforwardId X).inv.naturality]
    simp only [Functor.id_map, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl
  · have hz : IsZero ((ringComplexGodementResolution X).X n) := by
      apply HomologicalComplex.isZero_extend_X
      intro i hi
      change (i : ℤ) = n at hi
      omega
    exact hz.eq_of_src _ _

private theorem resmap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
    (r : SheafOfModules.unit Y.ringCatSheaf ⟶
      (pushforward g).obj (SheafOfModules.unit Z.ringCatSheaf)) (n : ℤ) :
    (resmap (g ≫ f) (q ≫ (pushforward f).map r ≫
      (pushforwardComp g f).hom.app (SheafOfModules.unit Z.ringCatSheaf))).f n =
        (resmap f q).f n ≫ (pushforward f).map ((resmap g r).f n) ≫
          (pushforwardComp g f).hom.app ((ringComplexGodementResolution Z).X n) := by
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [resmap_nat, resmap_nat, resmap_nat, cosmap_comp]
    simp only [Functor.map_comp, Category.assoc]
    have hc := (pushforwardComp g f).hom.naturality
      ((((alternatingCofaceMapComplex Z.Modules).obj (ringComplexGodementModel Z)).extendXIso
        ComplexShape.embeddingUpNat (i := m) rfl).inv)
    dsimp only [Functor.comp_map] at hc
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
    simp only [Functor.map_comp, Category.assoc]
    erw [hc]
  · have hz : IsZero ((ringComplexGodementResolution X).X n) := by
      apply HomologicalComplex.isZero_extend_X
      intro i hi
      change (i : ℤ) = n at hi
      omega
    exact hz.eq_of_src _ _

end
end AlgebraicGeometry
