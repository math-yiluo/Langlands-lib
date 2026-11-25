/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.RelativeTensorCoequalizer
import WeilConjectures.CategoryTheory.Monoidal.Mod.FreePresentation
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!

# Module objects in a closed symmetric monoidal Grothendieck abelian category

Let `C` be a closed symmetric monoidal Grothendieck abelian category whose tensor product is
additive, and let `R : C` be a commutative algebra object. The category `Mod C R` of
`R`-module objects is abelian (`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`) and
symmetric monoidal for the relative tensor product `⊗_R`
(`WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`). This file records that `Mod C R`
inherits the remaining properties of `C` needed by the K-flat machinery:

* `Mod.monoidalClosed`: `Mod C R` is closed monoidal;
* `Mod C R` is Grothendieck abelian, as an instance deduced from `Mod.isGrothendieckAbelian`;
* `Mod.hasFunctorialFlatResolution`: `Mod C R` admits functorial flat resolutions if `C` does.

## Proofs

* `Mod.monoidalClosed`: after forgetting the action, `N ⊗_R M` is the coequalizer of two maps
  `(N ⊗ R) ⊗ M ⇉ N ⊗ M`, natural in `N`, between functors that preserve colimits because `C` is
  closed. As `forget` reflects colimits, `- ⊗_R M` preserves them, and it is a left adjoint
  because `Mod C R` is Grothendieck abelian, hence has a separator.
* `Mod.hasFunctorialFlatResolution`: for `F : C`, the split coequalizer of the action gives
  `M ⊗_R (R ⊗ F) ≅ M ⊗ F` naturally in `M`, so `R ⊗ F` is flat in `Mod C R` when `F` is flat in
  `C`. A functorial flat resolution `P(M) ⟶ M` in `C` then gives the functorial epimorphism
  `R ⊗ P(M) ⟶ R ⊗ M ⟶ M` of `R`-modules.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The relative tensor product of module objects over a commutative algebra object in a closed
symmetric monoidal Grothendieck abelian category is closed. -/
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) where
  closed M := by
    -- Keep `[MonoidalPreadditive C]` out of the signature: closedness already gives it.
    rename_i hpre _ _ _ _
    clear hpre
    have : MonoidalPreadditive C := MonoidalClosed.monoidalPreadditive_of_braided
    have : IsGrothendieckAbelian.{v} (Mod C R) := isGrothendieckAbelian R
    let F₀ := forget R ⋙ MonoidalCategory.tensorRight R ⋙
      MonoidalCategory.tensorRight M.X
    let F₁ := forget R ⋙ MonoidalCategory.tensorRight M.X
    let f : F₀ ⟶ F₁ :=
      { app := fun N ↦ ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ ModObj.smul (M := R) (X := N'.X)) ▷ M.X =
            ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X ≫ φ.hom ▷ M.X
          rw [← comp_whiskerRight, ← comp_whiskerRight]
          congr 1
          rw [BraidedCategory.braiding_naturality_left_assoc, ← act_hom]
          simp only [Category.assoc] }
    let g : F₀ ⟶ F₁ :=
      { app := fun N ↦ (α_ N.X R M.X).hom ≫ N.X ◁ ModObj.smul (M := R) (X := M.X)
        naturality := by
          intro N N' φ
          change (φ.hom ▷ R) ▷ M.X ≫ (α_ N'.X R M.X).hom ≫
              N'.X ◁ ModObj.smul (M := R) (X := M.X) =
            ((α_ N.X R M.X).hom ≫ N.X ◁ ModObj.smul (M := R) (X := M.X)) ≫ φ.hom ▷ M.X
          rw [associator_naturality_left_assoc, ← whisker_exchange]
          simp only [Category.assoc] }
    let D := parallelPair f g
    have : PreservesColimitsOfSize.{v, v} D.flip :=
      ⟨fun {J} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun j ↦ by
        cases j
        · exact inferInstanceAs (PreservesColimitsOfShape J F₀)
        · exact inferInstanceAs (PreservesColimitsOfShape J F₁)⟩
    let e : D.flip ⋙ colim ≅ MonoidalCategory.tensorRight M ⋙ forget R :=
      NatIso.ofComponents
        (fun N ↦ HasColimit.isoOfNatIso (diagramIsoParallelPair (D.flip.obj N)) ≪≫
          IsColimit.coconePointUniqueUpToIso
            (t := Cofork.ofπ (tensorObjπ N M) (tensorObjπ_condition N M))
            (colimit.isColimit _) (isColimitTensorπ N M)) (by
        intro N N' φ
        apply colimit.hom_ext
        intro j
        simp only [Functor.comp_map, colim_map, Iso.trans_hom, Category.assoc,
          ι_colimMap_assoc, HasColimit.ι_isoOfNatIso_hom_assoc]
        cases j
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight]
          have h := congrArg (fun k ↦ k ≫ tensorObjπ N' M) (f.naturality φ)
          simp only [Category.assoc] at h
          change (φ.hom ▷ R) ▷ M.X ≫
              ((β_ N'.X R).hom ≫ ModObj.smul (M := R) (X := N'.X)) ▷ M.X ≫ tensorObjπ N' M =
            ((β_ N.X R).hom ≫ ModObj.smul (M := R) (X := N.X)) ▷ M.X ≫
              φ.hom ▷ M.X ≫ tensorObjπ N' M at h
          simpa only [comp_whiskerRight, Category.assoc] using h
        · simp [D, F₀, F₁, f, g, tensorObjπ_whiskerRight])
    have : PreservesColimitsOfSize.{v, v}
        (MonoidalCategory.tensorRight M ⋙ forget R) := preservesColimits_of_natIso e
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight M) :=
      preservesColimits_of_reflects_of_preserves _ (forget R)
    have : PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft M) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm
    have : (MonoidalCategory.tensorLeft M).IsLeftAdjoint :=
      isLeftAdjoint_of_preservesColimits_of_isSeparating
        (isSeparator_separator (Mod C R)) _
    exact
      { rightAdj := (MonoidalCategory.tensorLeft M).rightAdjoint
        adj := Adjunction.ofIsLeftAdjoint _ }


/-- The category of module objects over a commutative algebra object in a closed symmetric
monoidal Grothendieck abelian category is Grothendieck abelian, see `Mod.isGrothendieckAbelian`:
tensoring with an object is a left adjoint, so it preserves colimits. -/
instance : IsGrothendieckAbelian.{v} (Mod C R) :=
  isGrothendieckAbelian R

open MonObj in
section

/-- The free relative tensor product is the ordinary tensor product, by the split action
coequalizer. -/
private def freeTensorSplit (M : Mod C R) (F : C) :
    IsSplitCoequalizer
      ((α_ M.X R (R ⊗ F)).inv ≫ rightAct M ▷ (R ⊗ F))
      (M.X ◁ ((α_ R R F).inv ≫ μ[R] ▷ F))
      ((α_ M.X R F).inv ≫ rightAct M ▷ F) where
  rightSection := (unitRight M).hom ▷ F ≫ (α_ M.X R F).hom
  leftSection := M.X ◁ (((ρ_ R).inv ≫ R ◁ η[R]) ▷ F ≫ (α_ R R F).hom)
  condition := by
    have h : rightAct M ▷ R ≫ rightAct M =
        (α_ M.X R R).hom ≫ M.X ◁ μ[R] ≫ rightAct M := by
      rw [whiskerLeft_mul_rightAct, Iso.hom_inv_id_assoc]
    simp only [Category.assoc]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, h]
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    monoidal
  rightSection_π := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight]
    have h := congrArg Hom.hom (unitRight_rightActHom M)
    change (unitRight M).hom ≫ rightAct M = 𝟙 M.X at h
    rw [h, id_whiskerRight]
  leftSection_bottom := by
    rw [← MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight]
    rw [MonObj.mul_one, Iso.inv_hom_id, id_whiskerRight,
      MonoidalCategory.whiskerLeft_id]
  leftSection_top := by
    have h : rightAct M ≫ ((ρ_ M.X).inv ≫ M.X ◁ η[R]) =
        (ρ_ (M.X ⊗ R)).inv ≫ (M.X ⊗ R) ◁ η[R] ≫ rightAct M ▷ R := by
      rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc, ← whisker_exchange]
    change _ = ((α_ M.X R F).inv ≫ rightAct M ▷ F) ≫
      ((ρ_ M.X).inv ≫ M.X ◁ η[R]) ▷ F ≫ (α_ M.X R F).hom
    simp only [Category.assoc]
    conv_rhs => rw [← comp_whiskerRight_assoc, h]
    generalize rightAct M = a
    simp only [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_naturality_left]
    monoidal

/-- The split coequalizer with its two arrows in the tensor convention. -/
private def freeTensorCoforkIsColimit (M : Mod C R) (F : C) :
    IsColimit (Cofork.ofπ ((α_ M.X R F).inv ≫ rightAct M ▷ F)
      (freeTensorSplit M F).condition.symm) := by
  let h := freeTensorSplit M F
  refine Cofork.IsColimit.mk _ (fun s ↦ h.rightSection ≫ s.π) ?_ ?_
  · intro s
    change ((α_ M.X R F).inv ≫ rightAct M ▷ F) ≫ h.rightSection ≫ s.π = s.π
    rw [← h.leftSection_top_assoc, ← s.condition, h.leftSection_bottom_assoc]
  · intro s m hm
    rw [← hm]
    change m = h.rightSection ≫ ((α_ M.X R F).inv ≫ rightAct M ▷ F) ≫ m
    simpa only [Category.assoc] using
      ((congrArg (fun k : M.X ⊗ F ⟶ M.X ⊗ F ↦ k ≫ m) h.rightSection_π).trans
        (Category.id_comp m)).symm

/-- The underlying object of tensoring with a free module is the ambient tensor product. -/
private noncomputable def freeTensorUnderlyingIso (M : Mod C R) (F : C) :
    (M ⊗ (free R).obj F).X ≅ M.X ⊗ F :=
  (isColimitCoforkMapOfIsColimit (forget R) _
    (isColimitRelativeTensorCofork M ((free R).obj F))).coconePointUniqueUpToIso
      (freeTensorCoforkIsColimit M F)

omit [MonoidalPreadditive C] in
/-- The free-tensor comparison is induced by the right module action. -/
@[reassoc]
private lemma tensorπ_freeTensorUnderlyingIso_hom (M : Mod C R) (F : C) :
    tensorObjπ M ((free R).obj F) ≫ (freeTensorUnderlyingIso M F).hom =
      (α_ M.X R F).inv ≫ rightAct M ▷ F := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitCoforkMapOfIsColimit (forget R) _
      (isColimitRelativeTensorCofork M ((free R).obj F)))
    (freeTensorCoforkIsColimit M F) WalkingParallelPair.one

/-- Naturality of the free-tensor comparison. -/
private noncomputable def freeTensorForgetIso (F : C) :
    MonoidalCategory.tensorRight ((free R).obj F) ⋙ forget R ≅
      forget R ⋙ MonoidalCategory.tensorRight F :=
  NatIso.ofComponents (fun M ↦ freeTensorUnderlyingIso M F) (by
    intro M N f
    change (f ▷ (free R).obj F).hom ≫ (freeTensorUnderlyingIso N F).hom =
      (freeTensorUnderlyingIso M F).hom ≫ f.hom ▷ F
    rw [← cancel_epi (tensorObjπ M ((free R).obj F)),
      tensorObjπ_whiskerRight_assoc, tensorπ_freeTensorUnderlyingIso_hom,
      tensorπ_freeTensorUnderlyingIso_hom_assoc]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
      ← comp_whiskerRight]
    exact congrArg (fun k ↦ (α_ M.X R F).inv ≫ k ▷ F)
      (congrArg Hom.hom (rightActHom_naturality f)))

omit [MonoidalPreadditive C] in
/-- A free module on a flat ambient object is flat for the relative tensor product. -/
private lemma flat_free {F : C} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((free R).obj F) := by
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight F) := hF.2.1
  have : PreservesFiniteLimits
      (MonoidalCategory.tensorRight ((free R).obj F) ⋙ forget R) :=
    preservesFiniteLimits_of_natIso (freeTensorForgetIso F).symm
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight ((free R).obj F)) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (forget R)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft ((free R).obj F)) :=
    preservesFiniteLimits_of_natIso
      (BraidedCategory.tensorLeftIsoTensorRight ((free R).obj F)).symm
  simp only [ObjectProperty.flat, exactFunctor_iff]
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

end

/-- If `C` admits functorial flat resolutions, then so does `Mod C R`, by the free modules
`R ⊗ F` on flat objects `F` of `C`. -/
instance hasFunctorialFlatResolution [Abelian.HasFunctorialFlatResolution C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) := by
  -- Keep `[MonoidalPreadditive C]` out of the signature: closedness already gives it.
  rename_i hpre _ _ _ _ _
  clear hpre
  have : MonoidalPreadditive C := MonoidalClosed.monoidalPreadditive_of_braided
  obtain ⟨Λ⟩ := ‹Abelian.HasFunctorialFlatResolution C›
  have : (free R).IsLeftAdjoint := (freeForgetAdjunction R).isLeftAdjoint
  let F := forget R ⋙ Λ.F ⋙ ObjectProperty.flat.ι ⋙ free R
  let π : F ⟶ 𝟭 (Mod C R) :=
    Functor.whiskerRight (Functor.whiskerLeft (forget R) Λ.π) (free R) ≫
      (freeForgetAdjunction R).counit
  refine ⟨{ F := ObjectProperty.lift _ F ?_, π := π, epi_π_app := ?_ }⟩
  · intro M
    exact flat_free (Λ.F.obj ((forget R).obj M)).property
  · intro M
    change Epi ((free R).map (Λ.π.app ((forget R).obj M)) ≫
      (freeForgetAdjunction R).counit.app M)
    have : Epi (Λ.π.app ((forget R).obj M)) := inferInstance
    have : PreservesColimits (free R) :=
      (freeForgetAdjunction R).leftAdjoint_preservesColimits
    have : Epi ((free R).map (Λ.π.app ((forget R).obj M))) :=
      (free R).map_epi _
    exact epi_comp _ _

end CategoryTheory.Mod
