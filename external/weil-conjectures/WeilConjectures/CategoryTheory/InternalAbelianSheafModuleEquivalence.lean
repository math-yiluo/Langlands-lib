/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # Internal abelian module sheaves as sectionwise module sheaves

Source: Stacks Project, Tag 00YV, algebraic structures in a ringed topos.
(auxiliary; not a blueprint node).

We reconstruct the section rings and their modules from the tensor multiplication
and action. Presheaf module objects identify with sectionwise presheaf modules.
The monoidal sheafification adjunction then lifts to module objects; its unit is
invertible on an underlying sheaf. This gives the sectionwise sheaf equivalence,
with the original underlying abelian sheaves and restrictions.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped TensorProduct CategoryTheory.Obj
set_option backward.isDefEq.respectTransparency false
universe u
namespace CategoryTheory.InternalAbelianSheafModule
variable (R : AddCommGrpCat.{u}) [MonObj R]
@[instance_reducible] noncomputable def ring : Ring R := by
  let mul : R → R → R := fun a b ↦ (μ[R]).hom (a ⊗ₜ[ℤ] b)
  let one : R := (η[R]).hom (ULift.up 1)
  refine
    { (inferInstance : AddCommGroup R) with
      mul := mul
      one := one
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_ }
  · intro a b c
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc R) ((a ⊗ₜ[ℤ] b) ⊗ₜ[ℤ] c)
  · intro a
    have h := ConcreteCategory.congr_hom (MonObj.one_mul R) (ULift.up 1 ⊗ₜ[ℤ] a)
    change (μ[R]).hom ((η[R] ▷ R).hom (ULift.up 1 ⊗ₜ[ℤ] a)) =
      ((λ_ R).hom).hom (ULift.up 1 ⊗ₜ[ℤ] a) at h
    rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul] at h
    convert! h using 1; simp
  · intro a
    have h := ConcreteCategory.congr_hom (MonObj.mul_one R) (a ⊗ₜ[ℤ] ULift.up 1)
    change (μ[R]).hom ((R ◁ η[R]).hom (a ⊗ₜ[ℤ] ULift.up 1)) =
      ((ρ_ R).hom).hom (a ⊗ₜ[ℤ] ULift.up 1) at h
    rw [AddCommGrpCat.MonoidalCategory.whiskerLeft_tmul,
      AddCommGrpCat.MonoidalCategory.rightUnitor_hom_tmul] at h
    convert! h using 1; simp
  · intro a
    change (μ[R]).hom (0 ⊗ₜ[ℤ] a) = 0
    rw [TensorProduct.zero_tmul, map_zero]
  · intro a
    change (μ[R]).hom (a ⊗ₜ[ℤ] 0) = 0
    rw [TensorProduct.tmul_zero, map_zero]
  · intro a b c
    change (μ[R]).hom (a ⊗ₜ[ℤ] (b + c)) = _
    rw [TensorProduct.tmul_add, map_add]
    rfl
  · intro a b c
    change (μ[R]).hom ((a + b) ⊗ₜ[ℤ] c) = _
    rw [TensorProduct.add_tmul, map_add]
    rfl
@[instance_reducible] noncomputable def commRing [IsCommMonObj R] : CommRing R := by
  letI := ring R
  refine { ring R with mul_comm := ?_ }
  intro a b
  have h := ConcreteCategory.congr_hom (IsCommMonObj.mul_comm (X := R)) (a ⊗ₜ[ℤ] b)
  change (μ[R]).hom (((β_ R R).hom).hom (a ⊗ₜ[ℤ] b)) = (μ[R]).hom (a ⊗ₜ[ℤ] b) at h
  change (μ[R]).hom (b ⊗ₜ[ℤ] a) = (μ[R]).hom (a ⊗ₜ[ℤ] b) at h
  exact h.symm

noncomputable def ringHom {R S : AddCommGrpCat.{u}} [MonObj R] [MonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    letI := ring R
    letI := ring S
    R →+* S := by
  letI := ring R
  letI := ring S
  refine { f.hom with map_one' := ?_, map_mul' := ?_ }
  · exact ConcreteCategory.congr_hom (IsMonHom.one_hom f) (ULift.up 1)
  · intro a b
    exact ConcreteCategory.congr_hom (IsMonHom.mul_hom f) (a ⊗ₜ[ℤ] b)

noncomputable def monToRing : Mon AddCommGrpCat.{u} ⥤ RingCat.{u} where
  obj R := letI := ring R.X; RingCat.of R.X
  map {R S} f := by
    letI := ring R.X
    letI := ring S.X
    exact RingCat.ofHom (ringHom f.hom)
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl
noncomputable def commMonToRing : CommMon AddCommGrpCat.{u} ⥤ CommRingCat.{u} where
  obj R := letI := commRing R.X; CommRingCat.of R.X
  map {R S} f := by
    letI := commRing R.X
    letI := commRing S.X
    exact CommRingCat.ofHom (ringHom f.hom.hom)
  map_id R := by ext x; rfl
  map_comp f g := by ext x; rfl

@[instance_reducible] noncomputable def ordinaryModule (M : Mod AddCommGrpCat.{u} R) :
    letI := ring R
    Module R M.X := by
  letI := ring R
  refine
    { smul := fun r x ↦ (Mod.act M.X).hom (r ⊗ₜ[ℤ] x)
      one_smul := ?_
      mul_smul := ?_
      smul_zero := ?_
      smul_add := ?_
      zero_smul := ?_
      add_smul := ?_ }
  · intro r s x
    exact ConcreteCategory.congr_hom (Mod.mul_act M.X) ((r ⊗ₜ[ℤ] s) ⊗ₜ[ℤ] x)
  · intro x
    have h := ConcreteCategory.congr_hom (Mod.one_act (A := R) M.X)
      ((ULift.up (1 : ℤ)) ⊗ₜ[ℤ] x)
    change (Mod.act M.X).hom ((η[R] ▷ M.X).hom (ULift.up 1 ⊗ₜ[ℤ] x)) =
      ((λ_ M.X).hom).hom (ULift.up 1 ⊗ₜ[ℤ] x) at h
    rw [AddCommGrpCat.MonoidalCategory.whiskerRight_tmul,
      AddCommGrpCat.MonoidalCategory.leftUnitor_hom_tmul] at h
    convert! h using 1; simp
  · intro r
    change (Mod.act M.X).hom (r ⊗ₜ[ℤ] 0) = 0
    rw [TensorProduct.tmul_zero, map_zero]
  · intro r x y
    change (Mod.act M.X).hom (r ⊗ₜ[ℤ] (x + y)) = _
    rw [TensorProduct.tmul_add, map_add]
    rfl
  · intro r s x
    change (Mod.act M.X).hom ((r + s) ⊗ₜ[ℤ] x) = _
    rw [TensorProduct.add_tmul, map_add]
    rfl
  · intro x
    change (Mod.act M.X).hom (0 ⊗ₜ[ℤ] x) = 0
    rw [TensorProduct.zero_tmul, map_zero]

section Presheaf
universe v w
variable {C : Type v} [Category.{w} C]
variable (A : Cᵒᵖ ⥤ AddCommGrpCat.{u}) [MonObj A]
noncomputable def presheafRings : Cᵒᵖ ⥤ RingCat.{u} :=
  (Monoidal.monFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.obj
    (Mon.mk A) ⋙ monToRing

noncomputable def pointwiseMod (M : Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) A) (Z : Cᵒᵖ) :
    Mod AddCommGrpCat.{u}
      ((Monoidal.MonFunctorCategoryEquivalence.functorObjObj A Z).X) := by
  let AA := Monoidal.MonFunctorCategoryEquivalence.functorObjObj A Z
  letI : MonObj AA.X := AA.mon
  letI : ModObj AA.X (M.X.obj Z) :=
    ModObj.mk' AA.X ((Mod.act M.X).app Z)
      (congr_app (Mod.one_act (A := A) M.X) Z)
      (congr_app (Mod.mul_act (A := A) M.X) Z)
  exact { X := M.X.obj Z, mod := inferInstance }

noncomputable def presheafModules (M : Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) A) :
    PresheafOfModules.{u} (presheafRings A) := by
  letI (Z : Cᵒᵖ) : Module ((presheafRings A).obj Z) (M.X.obj Z) :=
    by
      exact ordinaryModule _ (pointwiseMod A M Z)
  refine PresheafOfModules.ofPresheaf M.X ?_
  intro Z Z' f r m
  have h := ConcreteCategory.congr_hom ((Mod.act M.X).naturality f) (r ⊗ₜ[ℤ] m)
  exact h.symm
noncomputable def ordinaryAction {S : Type u} [Ring S]
    {N : Type u} [AddCommGroup N] [Module S N] :
    AddCommGrpCat.of S ⊗ AddCommGrpCat.of N ⟶ AddCommGrpCat.of N := by
  let b : S →+ N →+ N :=
    { toFun := fun r ↦
        { toFun := fun m ↦ r • m
          map_zero' := smul_zero r
          map_add' := smul_add r }
      map_zero' := by ext m; exact zero_smul S m
      map_add' := by intro r s; ext m; exact add_smul r s m }
  exact AddCommGrpCat.ofHom (TensorProduct.liftAddHom b (by
    intro z r m
    change b (z • r) m = (b r) (z • m)
    rw [map_zsmul, map_zsmul]
    rfl))

@[simp] theorem ordinaryAction_tmul {S : Type u} [Ring S]
    {N : Type u} [AddCommGroup N] [Module S N] (r : S) (x : N) :
    (ordinaryAction (S := S) (N := N)).hom (r ⊗ₜ[ℤ] x) = r • x := rfl

noncomputable def internalPresheafAction (P : PresheafOfModules.{u} (presheafRings A)) :
    A ⊗ P.presheaf ⟶ P.presheaf where
  app Z := ordinaryAction (S := (presheafRings A).obj Z) (N := P.obj Z)
  naturality Z Z' f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext'
    intro r m
    exact (P.map_smul f r m).symm
theorem sectionOne_zsmul (Z : Cᵒᵖ) (z : ℤ) :
    (η[A].app Z).hom (ULift.up z) = z • (1 : (presheafRings A).obj Z) := by
  change (η[A].app Z).hom (ULift.up z) = z • (η[A].app Z).hom (ULift.up 1)
  have h := map_zsmul (η[A].app Z).hom z (ULift.up 1)
  change (η[A].app Z).hom (ULift.up (z * 1)) = _ at h
  simp only [_root_.mul_one] at h
  convert! h using 1

noncomputable def internalPresheafMod (P : PresheafOfModules.{u} (presheafRings A)) :
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) A := by
  let a := internalPresheafAction A P
  letI : ModObj A P.presheaf := ModObj.mk' A a (by
    apply NatTrans.ext
    funext Z
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext'
    intro z m
    change (a.app Z).hom ((η[A].app Z).hom z ⊗ₜ[ℤ] m) = z.down • m
    rw [show z = ULift.up z.down from rfl, sectionOne_zsmul]
    change (z.down • (1 : (presheafRings A).obj Z)) • m = z.down • m
    rw [smul_assoc, one_smul]) (by
    apply NatTrans.ext
    funext Z
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    let : MonObj (A.obj Z) :=
      (Monoidal.MonFunctorCategoryEquivalence.functorObjObj A Z).mon
    let : Ring (A.obj Z) := ring (A.obj Z)
    let : Module (A.obj Z) (P.presheaf.obj Z) := (P.obj Z).isModule
    apply TensorProduct.ext_threefold
    intro r s m
    change ((r : (presheafRings A).obj Z) * (s : (presheafRings A).obj Z)) •
      (m : P.obj Z) = (r : (presheafRings A).obj Z) •
        (s : (presheafRings A).obj Z) • (m : P.obj Z)
    exact mul_smul _ _ _)
  exact ⟨P.presheaf⟩
noncomputable def presheafModuleFunctor :
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) A ⥤ PresheafOfModules.{u} (presheafRings A) where
  obj M := presheafModules A M
  map {M N} f := PresheafOfModules.homMk f.hom (by
    intro Z r m
    exact ConcreteCategory.congr_hom (congr_app (Mod.act_hom f) Z) (r ⊗ₜ[ℤ] m))
  map_id M := by ext Z m; rfl
  map_comp f g := by ext Z m; rfl

noncomputable def internalPresheafMap
    {M N : Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) A}
    (f : presheafModules A M ⟶ presheafModules A N) : M ⟶ N :=
  Mod.homMk ((PresheafOfModules.toPresheaf (presheafRings A)).map f) (by
    apply NatTrans.ext
    funext Z
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.toIntLinearMap_injective
    apply TensorProduct.ext'
    intro r m
    exact (f.app Z).hom.map_smul r m)

noncomputable def presheafModuleFunctor_fullyFaithful :
    (presheafModuleFunctor A).FullyFaithful where
  preimage f := internalPresheafMap A f
  map_preimage f := by ext Z m; rfl
  preimage_map f := by apply Mod.hom_ext; ext Z m; rfl

noncomputable def presheafModuleFunctor_counit
    (P : PresheafOfModules.{u} (presheafRings A)) :
    (presheafModuleFunctor A).obj (internalPresheafMod A P) ≅ P := by
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    rfl
  · intro Z Z' f
    ext m
    rfl

end Presheaf

section Site
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
noncomputable def sectionRings (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R] : Cᵒᵖ ⥤ CommRingCat.{u} :=
  (Monoidal.commMonFunctorCategoryEquivalence Cᵒᵖ AddCommGrpCat.{u}).functor.obj
    ((sheafToPresheaf J AddCommGrpCat.{u}).mapCommMon.obj (CommMon.mk R)) ⋙ commMonToRing
noncomputable def sectionRingSheaf (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R] : Sheaf J CommRingCat.{u} := by
  refine ⟨sectionRings J R, ?_⟩
  let : Limits.PreservesLimitsOfSize.{w, max v w}
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
    Limits.preservesLimitsOfSize_of_univLE.{max v w, max v w} _
  apply (Presheaf.isSheaf_iff_isSheaf_comp J _
    (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u})).2
  change Presheaf.IsSheaf J R.obj
  exact R.property
noncomputable def sheafModuleReflector (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] :
    Mod (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ((sheafToPresheaf J AddCommGrpCat.{u}).obj R) ⥤
      Mod (Sheaf J AddCommGrpCat.{u}) R := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let ψ := (adj.homEquiv _ _).symm (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))
  have hψ : ψ = adj.counit.app R := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  exact adj.modLeft (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))

noncomputable def sheafModuleInclusion (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] :=
  (sheafToPresheaf J AddCommGrpCat.{u}).mapMod R

noncomputable def sheafModuleInclusion_fullyFaithful
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] :
    (sheafModuleInclusion J R).FullyFaithful where
  preimage {M N} f := by
    dsimp only [sheafModuleInclusion] at f
    refine Mod.homMk ⟨f.hom⟩ ?_
    apply Sheaf.tensor_hom_ext
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
    have h := Mod.act_hom f
    simp only [Functor.act_mapMod_obj, Category.assoc] at h
    convert! h using 1
  map_preimage f := by apply Mod.hom_ext; rfl
  preimage_map f := by apply Mod.hom_ext; rfl

noncomputable def sectionModuleFunctor (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf J AddCommGrpCat.{u}) R ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R)) where
  obj M :=
    { val := (presheafModuleFunctor ((sheafToPresheaf J AddCommGrpCat.{u}).obj R)).obj
        ((sheafModuleInclusion J R).obj M)
      isSheaf := M.X.property }
  map f := ⟨(presheafModuleFunctor _).map ((sheafModuleInclusion J R).map f)⟩
  map_id M := by ext Z m; rfl
  map_comp f g := by ext Z m; rfl

noncomputable def sectionModuleFunctor_fullyFaithful
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R] :
    (sectionModuleFunctor J R).FullyFaithful where
  preimage f := (sheafModuleInclusion_fullyFaithful J R).preimage
    (internalPresheafMap _ f.val)
  map_preimage f := by ext Z m; rfl
  preimage_map f := by apply Mod.hom_ext; ext Z m; rfl

noncomputable def liftedSheafModule (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R]
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) : Mod (Sheaf J AddCommGrpCat.{u}) R :=
  (sheafModuleReflector J R).obj
    (internalPresheafMod ((sheafToPresheaf J AddCommGrpCat.{u}).obj R) M.val)

noncomputable def presheafSheafificationModuleUnit (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R]
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) :
    internalPresheafMod ((sheafToPresheaf J AddCommGrpCat.{u}).obj R) M.val ⟶
      (sheafModuleInclusion J R).obj (liftedSheafModule J R M) := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let ψ := (adj.homEquiv _ _).symm (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))
  have hψ : ψ = adj.counit.app R := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  let e := adj.modAdjunction (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))
  let N := internalPresheafMod ((sheafToPresheaf J AddCommGrpCat.{u}).obj R) M.val
  exact e.unit.app N ≫ (Mod.comapId _).hom.app _

lemma presheafSheafificationModuleUnit_hom (R : Sheaf J AddCommGrpCat.{u})
    [MonObj R] [IsCommMonObj R]
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) :
    (presheafSheafificationModuleUnit J R M).hom = toSheafify J M.val.presheaf := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{u}
  let ψ := (adj.homEquiv _ _).symm (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))
  have hψ : ψ = adj.counit.app R := by simp [ψ, Adjunction.homEquiv_counit]
  have : IsIso ψ := by rw [hψ]; infer_instance
  have : IsMonHom ψ := by rw [hψ]; infer_instance
  let e := adj.modAdjunction (𝟙 ((sheafToPresheaf J AddCommGrpCat.{u}).obj R))
  let N := internalPresheafMod ((sheafToPresheaf J AddCommGrpCat.{u}).obj R) M.val
  have hunit : (e.unit.app N).hom = toSheafify J M.val.presheaf := by
    rw [← e.homEquiv_id N]
    change ((adj.modAdjunction _).homEquiv N _ (𝟙 _)).hom = _
    rw [Adjunction.modAdjunction_homEquiv_apply_hom]
    change adj.homEquiv _ _ (𝟙 _) = _
    simp only [Adjunction.homEquiv_unit]
    rfl
  change ((e.unit.app N) ≫ (Mod.comapId _).hom.app _).hom = _
  change (e.unit.app N).hom ≫ 𝟙 _ = _
  rw [Category.comp_id, hunit]

noncomputable def sectionModuleFunctor_counit
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (sectionRingSheaf J R))) :
    (sectionModuleFunctor J R).obj (liftedSheafModule J R M) ≅ M := by
  let A := (sheafToPresheaf J AddCommGrpCat.{u}).obj R
  let N := internalPresheafMod A M.val
  let u := presheafSheafificationModuleUnit J R M
  have hu : IsIso u.hom := by
    dsimp only [u]
    rw [presheafSheafificationModuleUnit_hom]
    exact isIso_toSheafify J M.isSheaf
  have : IsIso ((Mod.forget A).map u) := hu
  have : IsIso u := isIso_of_reflects_iso u (Mod.forget A)
  let p := (presheafModuleFunctor A).mapIso (asIso u)
  let z := p.symm ≪≫ presheafModuleFunctor_counit A M.val
  exact
    { hom := ⟨z.hom⟩
      inv := ⟨z.inv⟩
      hom_inv_id := SheafOfModules.hom_ext z.hom_inv_id
      inv_hom_id := SheafOfModules.hom_ext z.inv_hom_id }

/-- The existing equivalence construction, retained as a named record.
Source: Stacks 00YV (auxiliary; not a blueprint node).
This is the original equivalence with no choice or construction changed. -/
noncomputable def sectionModuleEquivalenceCore
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf J AddCommGrpCat.{u}) R ≌
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R)) := by
  let F := sectionModuleFunctor J R
  let : F.Full := (sectionModuleFunctor_fullyFaithful J R).full
  let : F.Faithful := (sectionModuleFunctor_fullyFaithful J R).faithful
  let : F.EssSurj :=
    ⟨fun M ↦ ⟨liftedSheafModule J R M, ⟨sectionModuleFunctor_counit J R M⟩⟩⟩
  let : F.IsEquivalence := {}
  exact F.asEquivalence


/-- Internal modules over a commutative monoid in abelian sheaves are sectionwise
module sheaves over its reconstructed ring sheaf, with unchanged underlying sheaves.
Source: Stacks Project, Tag 00YV, algebraic structures in a ringed topos.
(auxiliary; not a blueprint node).
The sectionwise functor is fully faithful by the tensor-sheafification adjunction.
Every sectionwise module lifts by monoidal sheafification; the adjunction unit is
invertible since its underlying presheaf already is a sheaf. -/
noncomputable def sectionModuleEquivalence
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R] :
    Mod (Sheaf J AddCommGrpCat.{u}) R ≌
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (sectionRingSheaf J R)) :=
  { sectionModuleEquivalenceCore J R with functor := sectionModuleFunctor J R }

end Site
end CategoryTheory.InternalAbelianSheafModule
