/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
Declarations of ours that lived in the upstream file
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` (moved out by the
scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live).
-/

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

## Sorried input

The instances `Mod.monoidalClosed` and `Mod.hasFunctorialFlatResolution` are currently `sorry`ed.
The intended arguments are:

* The internal hom `Hom_R(M, N)` is the equalizer of the two maps `[M, N] ⇉ [R ⊗ M, N]`, adjoint
  to `R ⊗ M ⊗ [M, N] ⟶ R ⊗ N ⟶ N` and to `R ⊗ M ⊗ [M, N] ⟶ M ⊗ [M, N] ⟶ N`, with the
  `R`-action induced by that of `N`.
* If `F` is flat in `C`, then `R ⊗ F` is flat in `Mod C R` because `(R ⊗ F) ⊗_R M ≅ F ⊗ M`; and
  a functorial flat resolution `P(M) ⟶ M` in `C` gives the functorial epimorphism
  `R ⊗ P(M) ⟶ R ⊗ M ⟶ M` of `R`-modules.

-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The quotient map defining the relative tensor product is linear in its first factor. -/
private noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
private noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
private noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

/-- The previously constructed coequalizer tensor functor agrees with the monoidal tensor. -/
private noncomputable def relativeTensorRightIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents
    (fun M ↦ by
      change colimit ((tensorLeftDiagram R N).flip.obj M) ≅ M ⊗ N
      exact HasColimit.isoOfNatIso
        (diagramIsoParallelPair ((tensorLeftDiagram R N).flip.obj M)) ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso (isColimitRelativeTensorCofork M N)) (by
    intro M M' f
    apply colimit.hom_ext
    intro j
    simp only [id_eq, Iso.trans_hom, tensorLeft, Functor.comp_map, colim_map, Category.assoc,
      ι_colimMap_assoc, HasColimit.ι_isoOfNatIso_hom_assoc]
    cases j <;> apply Mod.hom_ext <;>
      simp [relativeTensorCofork, relativeTensorπ, tensorObjπ_whiskerRight])

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

end CategoryTheory.Mod
