/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Retract
import all WeilConjectures.Algebra.Homology.RingedSitePointTensor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.CategoryTheory.Sites.InverseImageFreeModule
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Finitely presented point modules as retracts of global stalks -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.RingedSitePoint

private def freeDesc
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w))
    (M : SheafOfModules.{w} (SheafFreeModule.ring R))
    (g : T ⟶ (SheafOfModules.toSheaf _ ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj M) :
    (SheafFreeModule.free R).obj T ⟶ M := by
  let adj := (PresheafOfModules.freeAdjunction (SheafFreeModule.ring R).obj).comp
    (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 (SheafFreeModule.ring R).obj))
  exact (adj.homEquiv T.obj M).symm g.hom

private theorem freeDesc_generator
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w))
    (M : SheafOfModules.{w} (SheafFreeModule.ring R))
    (g : T ⟶ (SheafOfModules.toSheaf _ ⋙
      sheafCompose J (forget AddCommGrpCat.{w})).obj M) :
    SheafFreeModule.generatorRaw R T ≫
      (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat.{w})).map
        (freeDesc R T M g) = g := by
  let adj := (PresheafOfModules.freeAdjunction (SheafFreeModule.ring R).obj).comp
    (PresheafOfModules.sheafificationAdjunction.{w} (𝟙 (SheafFreeModule.ring R).obj))
  have h := (adj.homEquiv T.obj M).apply_symm_apply g.hom
  apply Sheaf.hom_ext
  exact h

private def scalarGenerator
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w))
    (a : T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R) :
    T ⟶ (SheafOfModules.toSheaf _ ⋙ sheafCompose J (forget AddCommGrpCat.{w})).obj
      ((SheafFreeModule.free R).obj T) where
  hom :=
    { app := fun U ↦ ↾fun t ↦ (@id (R.obj.obj U) (a.hom.app U t)) •
        (@id (((SheafFreeModule.free R).obj T).val.obj U)
          ((SheafFreeModule.generatorRaw R T).hom.app U t))
      naturality := by
        intro U V f
        ext t
        have ha := NatTrans.naturality_apply a.hom f t
        have hg := NatTrans.naturality_apply (SheafFreeModule.generatorRaw R T).hom f t
        dsimp at ha hg ⊢
        rw [ha, hg]
        exact (((SheafFreeModule.free R).obj T).val.map_smul f _ _).symm }

private def scalarFree
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w))
    (a : T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R) :
    (SheafFreeModule.free R).obj T ⟶ (SheafFreeModule.free R).obj T :=
  freeDesc R T _ (scalarGenerator R T a)

private theorem scalarFree_generator
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (T : Sheaf J (Type w))
    (a : T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R)
    (U : Cᵒᵖ) (t : T.obj.obj U) :
    (scalarFree R T a).val.app U ((SheafFreeModule.generatorRaw R T).hom.app U t) =
      (@id (R.obj.obj U) (a.hom.app U t)) •
        (@id (((SheafFreeModule.free R).obj T).val.obj U)
          ((SheafFreeModule.generatorRaw R T).hom.app U t)) := by
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k ↦ k.hom)
      (freeDesc_generator R T _ (scalarGenerator R T a))) U) t

private def freePointIso (A : CommRingCat.{w}) (X : Type w) :
    (ModuleCat.free A).obj X ≅
      (moduleEval A).obj ((SheafFreeModule.free (pointRing A)).obj
        ((constant (Type w)).obj X)) := by
  let P := PresheafOfModules.freeObj
    (R := ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A)).obj)
      (((constant (Type w)).obj X).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A)).obj)
  have : IsIso (adj.unit.app P) :=
    adj.isIso_unit_app_of_iso (X := ⟨P, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  exact (PresheafOfModules.evaluation _ point).mapIso (asIso (adj.unit.app P))

private theorem free_stalk
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p) (T : Sheaf J (Type w)) :
    ∃ e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
        s.modules.obj ((SheafFreeModule.free R).obj T),
      ∀ x : p.inverse.obj T,
        e.hom (ModuleCat.freeMk x) =
          (s.moduleUnderlying.inv.app ((SheafFreeModule.free R).obj T))
            (p.inverse.map (SheafFreeModule.generatorRaw R T) x) := by
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : (constant (Type w)).IsEquivalence := setEquivalence.isEquivalence_inverse
  have : PreservesFiniteLimits (p.inverse ⋙ constant (Type w)) :=
    comp_preservesFiniteLimits _ _
  let f : GeometricMorphism
      (Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{w + 1})) (Type w))
      (Sheaf J (Type w)) :=
    { inverse := p.inverse ⋙ constant (Type w)
      direct := setEquivalence.functor ⋙ p.direct
      adj := p.adj.comp setEquivalence.symm.toAdjunction
      leftExact := inferInstance }
  let I := SheafOfModules.inverseImageOfUniverses_adapted (pointInverse s)
  obtain ⟨e, he, _⟩ := SheafFreeModule.inverseFreeModule_existsUnique f I T
  refine ⟨freePointIso s.ring (p.inverse.obj T) ≪≫
    ((moduleEval s.ring).mapIso e).symm, ?_⟩
  intro x
  dsimp only [SheafFreeModule.IsComparison] at he
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun k ↦ k.hom) he) point) x
  dsimp [SheafFreeModule.IsComparison, SheafFreeModule.comparison] at h
  apply (((moduleEval s.ring).mapIso e).toLinearEquiv).injective
  change ((moduleEval s.ring).mapIso e).hom
    (((moduleEval s.ring).mapIso e).inv
      ((freePointIso s.ring (p.inverse.obj T)).hom (ModuleCat.freeMk x))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  let U := SheafOfModules.toSheaf
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  let d := Functor.isoWhiskerLeft U (SheafOfModules.sheafUliftIso_adapted J
    AddCommGrpCat.{w} (forget AddCommGrpCat.{w}))
  have hg : SheafFreeModule.generator R T ≫ (d.app ((SheafFreeModule.free R).obj T)).hom =
      SheafFreeModule.generatorRaw R T := by
    ext V z
    rfl
  change ULift.up
    (e.hom.val.app point ((s.moduleUnderlying.inv.app ((SheafFreeModule.free R).obj T))
      (p.inverse.map (d.app ((SheafFreeModule.free R).obj T)).hom
        (p.inverse.map (SheafFreeModule.generator R T) x)))) =
    ULift.up ((freePointIso s.ring (p.inverse.obj T)).hom (ModuleCat.freeMk x)) at h
  have hcomp : p.inverse.map (d.app ((SheafFreeModule.free R).obj T)).hom
        (p.inverse.map (SheafFreeModule.generator R T) x) =
      p.inverse.map (SheafFreeModule.generatorRaw R T) x := by
    rw [← ConcreteCategory.comp_apply, ← p.inverse.map_comp, hg]
  rw [hcomp] at h
  exact (congrArg ULift.down h).symm

private theorem scalarFree_stalk
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p) (T : Sheaf J (Type w))
    (a : T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R)
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T))
    (he : ∀ x : p.inverse.obj T,
      e.hom (ModuleCat.freeMk x) =
        (s.moduleUnderlying.inv.app ((SheafFreeModule.free R).obj T))
          (p.inverse.map (SheafFreeModule.generatorRaw R T) x))
    (x : p.inverse.obj T) :
    s.modules.map (scalarFree R T a) (e.hom (ModuleCat.freeMk x)) =
      (@id s.ring (s.ringUnderlying.hom (p.inverse.map a x))) •
        (e.hom (ModuleCat.freeMk x)) := by
  let F := (SheafFreeModule.free R).obj T
  let U := SheafOfModules.toSheaf (SheafFreeModule.ring R) ⋙
    sheafCompose J (forget AddCommGrpCat.{w})
  let g := SheafFreeModule.generatorRaw R T
  have h := s.moduleSMul F T a g (g ≫ U.map (scalarFree R T a))
    (scalarFree_generator R T a) x
  have hn := ConcreteCategory.congr_hom
    (s.moduleUnderlying.inv.naturality (scalarFree R T a)) (p.inverse.map g x)
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at h
  rw [he x]
  exact hn.symm.trans h

section Matrix

attribute [local instance] Classical.propDecidable

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
  {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
  (s : RingedSitePoint R p) (T : Sheaf J (Type w))

private theorem matrix_parameter {ι κ : Type w} [Finite ι] [Finite κ]
    (a : κ → ι → s.ring) :
    ∃ (T : Sheaf J (Type w))
      (c : κ → ι → (T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R))
      (x : p.inverse.obj T),
      ∀ j i, s.ringUnderlying.hom (p.inverse.map (c j i) x) = a j i := by
  have : PreservesFiniteLimits p.inverse := p.leftExact
  let U := (sheafCompose J (forget CommRingCat.{w})).obj R
  let D : κ × ι → Sheaf J (Type w) := fun _ ↦ U
  let Z := ∏ᶜ D
  let z : PUnit.{w + 1} ⟶ ∏ᶜ (fun _ : κ × ι ↦ p.inverse.obj U) :=
    Pi.lift (fun ji ↦ ↾fun _ ↦ s.ringUnderlying.inv (a ji.1 ji.2))
  let g : PUnit.{w + 1} ⟶ p.inverse.obj Z :=
    z ≫ inv (piComparison p.inverse D)
  refine ⟨Z, fun j i ↦ Pi.π D (j, i), g PUnit.unit, ?_⟩
  intro j i
  have hz : g ≫ p.inverse.map (Pi.π D (j, i)) =
      (↾fun _ : PUnit.{w + 1} ↦ s.ringUnderlying.inv (a j i)) := by
    dsimp only [g]
    rw [← piComparison_comp_π]
    simp [z, D, Category.assoc]
  have hv := ConcreteCategory.congr_hom hz PUnit.unit
  change s.ringUnderlying.hom
    (p.inverse.map (Pi.π D (j, i)) (g PUnit.unit)) = a j i
  have hv' : p.inverse.map (Pi.π D (j, i)) (g PUnit.unit) =
      s.ringUnderlying.inv (a j i) := hv
  rw [hv']
  exact Iso.inv_hom_id_apply _ _

private local instance (ι : Type w) :
    HasColimitsOfShape (Discrete ι) (SheafOfModules.{w} (SheafFreeModule.ring R)) := by
  let : HasColimitsOfShape (Discrete ι)
      (PresheafOfModules.{w} (SheafFreeModule.ring R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
    _ _

private abbrev freePower (ι : Type w) :=
  ∐ fun _ : ι ↦ (SheafFreeModule.free R).obj T

private def powerInclude
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T)) {ι : Type w} (x : p.inverse.obj T) :
    (ModuleCat.free s.ring).obj ι ⟶ s.modules.obj (freePower (R := R) T ι) :=
  ModuleCat.freeDesc (R := s.ring) (↾fun i ↦
    s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
      (e.hom (ModuleCat.freeMk (R := s.ring) x)))

private def powerProject
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T)) {ι : Type w} (x : p.inverse.obj T) :
    s.modules.obj (freePower (R := R) T ι) ⟶ (ModuleCat.free s.ring).obj ι := by
  classical
  have := preservesColimits s
  exact inv (sigmaComparison s.modules (fun _ : ι ↦ (SheafFreeModule.free R).obj T)) ≫
    Sigma.desc (fun i ↦ e.inv ≫ ModuleCat.freeDesc (R := s.ring) (↾fun y ↦
      if y = x then ModuleCat.freeMk (R := s.ring) i else 0))

private theorem powerInclude_generator
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T))
    {ι : Type w} (x : p.inverse.obj T) (i : ι) :
    powerInclude s T e x (ModuleCat.freeMk (R := s.ring) i) =
      s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
        (e.hom (ModuleCat.freeMk (R := s.ring) x)) := by
  simp [powerInclude]

private theorem powerProject_generator
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T)) {ι : Type w} (x y : p.inverse.obj T) (i : ι) :
    powerProject s T e x
      (s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
        (e.hom (ModuleCat.freeMk (R := s.ring) y))) =
      if y = x then ModuleCat.freeMk (R := s.ring) i else 0 := by
  classical
  have := preservesColimits s
  have hi :
      s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i) ≫
        powerProject s T e x =
      e.inv ≫ ModuleCat.freeDesc (R := s.ring) (↾fun y ↦
        if y = x then ModuleCat.freeMk (R := s.ring) i else 0) := by
    simp [powerProject]
  have h := ConcreteCategory.congr_hom hi (e.hom (ModuleCat.freeMk (R := s.ring) y))
  simpa only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply,
    ModuleCat.freeDesc_apply, TypeCat.ofHom_apply] using h

private theorem powerInclude_project
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T)) {ι : Type w} (x : p.inverse.obj T) :
    powerInclude s T e (ι := ι) x ≫ powerProject s T e x = 𝟙 _ := by
  classical
  apply ModuleCat.free_hom_ext
  intro i
  simp only [ConcreteCategory.comp_apply, powerInclude, ModuleCat.freeDesc_apply,
    TypeCat.ofHom_apply, powerProject_generator, ite_true, ConcreteCategory.id_apply]

private theorem power_hom_ext
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T)) {ι : Type w} {N : ModuleCat.{w} s.ring}
    (f g : s.modules.obj (freePower (R := R) T ι) ⟶ N)
    (h : ∀ (i : ι) (y : p.inverse.obj T),
      f (s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
          (e.hom (ModuleCat.freeMk (R := s.ring) y))) =
      g (s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
          (e.hom (ModuleCat.freeMk (R := s.ring) y)))) : f = g := by
  have := preservesColimits s
  apply (cancel_epi (sigmaComparison s.modules
    (fun _ : ι ↦ (SheafFreeModule.free R).obj T))).1
  apply Sigma.hom_ext
  intro i
  simp only [ι_comp_sigmaComparison_assoc]
  apply (cancel_epi e.hom).1
  apply ModuleCat.free_hom_ext
  intro y
  exact h i y

private def matrixMap {ι κ : Type w} [Fintype κ]
    (c : κ → ι → (T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R)) :
    freePower (R := R) T ι ⟶ freePower (R := R) T κ :=
  Sigma.desc fun i ↦ ∑ j : κ,
    scalarFree R T (c j i) ≫ Sigma.ι (fun _ : κ ↦ (SheafFreeModule.free R).obj T) j

private theorem matrixMap_generator
    (e : (ModuleCat.free s.ring).obj (p.inverse.obj T) ≅
      s.modules.obj ((SheafFreeModule.free R).obj T))
    (he : ∀ x : p.inverse.obj T,
      e.hom (ModuleCat.freeMk (R := s.ring) x) =
        (s.moduleUnderlying.inv.app ((SheafFreeModule.free R).obj T))
          (p.inverse.map (SheafFreeModule.generatorRaw R T) x))
    {ι κ : Type w} [Fintype κ]
    (c : κ → ι → (T ⟶ (sheafCompose J (forget CommRingCat.{w})).obj R))
    (i : ι) (y : p.inverse.obj T) :
    s.modules.map (matrixMap T c)
      (s.modules.map (Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i)
        (e.hom (ModuleCat.freeMk (R := s.ring) y))) =
      ∑ j : κ, (@id s.ring (s.ringUnderlying.hom (p.inverse.map (c j i) y))) •
        (s.modules.map (Sigma.ι (fun _ : κ ↦ (SheafFreeModule.free R).obj T) j)
          (e.hom (ModuleCat.freeMk (R := s.ring) y))) := by
  have hm : Sigma.ι (fun _ : ι ↦ (SheafFreeModule.free R).obj T) i ≫
      matrixMap T c = ∑ j : κ,
        scalarFree R T (c j i) ≫
          Sigma.ι (fun _ : κ ↦ (SheafFreeModule.free R).obj T) j := by
    simp [matrixMap]
  have hs := congrArg s.modules.map hm
  simp only [Functor.map_comp, Functor.map_sum] at hs
  have hv := ConcreteCategory.congr_hom hs
    (e.hom (ModuleCat.freeMk (R := s.ring) y))
  simp only [ConcreteCategory.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply] at hv
  rw [hv]
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarFree_stalk s T (c j i) e he y, map_smul]

private theorem presentation_retract {ι κ : Type w} [Finite ι] [Finite κ]
    (f : (ModuleCat.free s.ring).obj ι ⟶ (ModuleCat.free s.ring).obj κ) :
    ∃ F : SheafOfModules.{w} (SheafFreeModule.ring R),
      Nonempty (Retract (cokernel f) (s.modules.obj F)) := by
  classical
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let a : κ → ι → s.ring := fun j i ↦ (@id (κ →₀ s.ring) (f (ModuleCat.freeMk i))) j
  obtain ⟨T, c, x, hx⟩ := matrix_parameter s a
  obtain ⟨e, he⟩ := free_stalk s T
  let α := matrixMap T c
  let ui := powerInclude s T e (ι := ι) x
  let uk := powerInclude s T e (ι := κ) x
  let ri := powerProject s T e (ι := ι) x
  let rk := powerProject s T e (ι := κ) x
  have hf (i : ι) : f (ModuleCat.freeMk i) =
      ∑ j : κ, a j i • ModuleCat.freeMk j := by
    apply Finsupp.ext
    intro j
    simp [a, ModuleCat.freeMk, ModuleCat.free]
  have hi : ui ≫ s.modules.map α = f ≫ uk := by
    apply ModuleCat.free_hom_ext
    intro i
    change s.modules.map α (ui (ModuleCat.freeMk i)) = uk (f (ModuleCat.freeMk i))
    rw [powerInclude_generator, matrixMap_generator s T e he c, hf]
    simp only [uk, map_sum, map_smul, powerInclude_generator, hx, id_eq]
  have hr : ri ≫ f = s.modules.map α ≫ rk := by
    apply power_hom_ext s T e
    intro i y
    change f (ri (s.modules.map (Sigma.ι _ i) (e.hom (ModuleCat.freeMk y)))) =
      rk (s.modules.map α (s.modules.map (Sigma.ι _ i) (e.hom (ModuleCat.freeMk y))))
    rw [powerProject_generator, matrixMap_generator s T e he c]
    simp only [rk, map_sum, map_smul, powerProject_generator]
    by_cases hy : y = x
    · subst y
      simpa only [ite_true, hx, id_eq] using hf i
    · simp [hy]
  let r : RetractArrow f (s.modules.map α) :=
    { i := Arrow.homMk ui uk hi
      r := Arrow.homMk ri rk hr
      retract := by
        ext : 1
        · exact powerInclude_project s T e x
        · exact powerInclude_project s T e x }
  have := preservesColimits s
  let rc := Retract.map r (coker (C := ModuleCat.{w} s.ring))
  refine ⟨cokernel α, ⟨rc.trans (Retract.ofIso (PreservesCokernel.iso s.modules α).symm)⟩⟩

end Matrix

/-- Any finitely presented stalk module is a retract of the stalk of a global module sheaf.
Source: Stacks Project, Cohomology on Sites, Tag 0DEN, finite-presentation descent,
with extension by zero of the local realization.
(auxiliary; not a blueprint node)

Proof: choose a finite presentation of M. On the sheaf of all matrices of its fixed
finite size, form the universal matrix cokernel: its rows and columns are copies
of the free module sheaf on this parameter sheaf, and its entries multiply a
parameter's generator by the corresponding coordinate. Finite-product preservation
lifts the chosen matrix to a point of the parameter sheaf. Normalized inverse image
of free modules identifies the stalk matrix with the direct sum of all matrices
parametrized by points of that sheaf. Inclusion of the chosen summand and projection
onto it commute with the presentation maps and compose to the identity. Apply
cokernels, which commute with exact module inverse image, to obtain the retract.
Empty row or column sets cause no exception: the parameter sheaf is terminal and
its inverse image has one point. -/
theorem finitePresentation_retract
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
    {p : GeometricMorphism (Type w) (Sheaf J (Type w))}
    (s : RingedSitePoint R p) (M : ModuleCat.{w} s.ring)
    (hM : Module.FinitePresentation s.ring M) :
    ∃ F : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      Nonempty (Retract M (s.modules.obj F)) := by
  classical
  have := hM
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' s.ring M
  let en (k : ℕ) : (ModuleCat.free s.ring).obj (ULift.{w} (Fin k)) ≃ₗ[s.ring]
      (Fin k → s.ring) :=
    Finsupp.linearEquivFunOnFinite s.ring s.ring (ULift.{w} (Fin k)) ≪≫ₗ
      LinearEquiv.funCongrLeft s.ring s.ring Equiv.ulift.symm
  let f' : (ModuleCat.free s.ring).obj (ULift.{w} (Fin n)) ⟶ M :=
    ModuleCat.ofHom (f.comp (en n).toLinearMap)
  let g' : (ModuleCat.free s.ring).obj (ULift.{w} (Fin m)) ⟶
      (ModuleCat.free s.ring).obj (ULift.{w} (Fin n)) :=
    ModuleCat.ofHom ((en n).symm.toLinearMap.comp (g.comp (en m).toLinearMap))
  have hf' : Function.Surjective f'.hom := hf.comp (en n).surjective
  have hg' : Function.Exact g'.hom f'.hom := by
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (hg ((en n) y)).1 hy
      refine ⟨(en m).symm z, ?_⟩
      apply (en n).injective
      simpa only [g', ModuleCat.hom_ofHom, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hz
    · rintro ⟨z, rfl⟩
      change f ((en n) ((en n).symm (g ((en m) z)))) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hg.apply_apply_eq_zero _
  let ec : cokernel g' ≅ M :=
    (cokernelIsCokernel g').coconePointUniqueUpToIso
      (ModuleCat.isColimitCokernelCofork g' f' hg' hf')
  obtain ⟨F, ⟨r⟩⟩ := presentation_retract s g'
  exact ⟨F, ⟨(Retract.ofIso ec.symm).trans r⟩⟩

end CategoryTheory.RingedSitePoint
