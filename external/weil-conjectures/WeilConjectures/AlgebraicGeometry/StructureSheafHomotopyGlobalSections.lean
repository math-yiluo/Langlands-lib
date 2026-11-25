/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single

/-! # Evaluation at one on homotopy classes of structure-sheaf maps

Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Lift chain maps and homotopies componentwise using the same inverse on each Hom set.
set_option backward.isDefEq.respectTransparency false in
private theorem map_homotopy_bijective
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type*} {c : ComplexShape ι} (F : C ⥤ D) [F.Additive]
    (K : HomologicalComplex C c)
    (h : ∀ i (Y : C), Function.Bijective
      (F.map : (K.X i ⟶ Y) → (F.obj (K.X i) ⟶ F.obj Y)))
    (L : HomologicalComplex C c) :
    Function.Bijective ((F.mapHomotopyCategory c).map :
      ((HomotopyCategory.quotient C c).obj K ⟶
        (HomotopyCategory.quotient C c).obj L) →
      ((F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj K) ⟶
        (F.mapHomotopyCategory c).obj ((HomotopyCategory.quotient C c).obj L))) := by
  classical
  let e (i : ι) (Y : C) := Equiv.ofBijective _ (h i Y)
  have he (i : ι) (Y : C) (f : F.obj (K.X i) ⟶ F.obj Y) :
      F.map ((e i Y).symm f) = f := (e i Y).apply_symm_apply f
  constructor
  · intro f g hfg
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective g
    let H := HomotopyCategory.homotopyOfEq _ _ hfg
    apply HomotopyCategory.eq_of_homotopy
    refine { hom := fun i j => (e i (L.X j)).symm (H.hom i j)
             zero := ?_, comm := ?_ }
    · intro i j hij
      apply (h i (L.X j)).1
      simp only [he, Functor.map_zero]
      exact H.zero i j hij
    · intro i
      apply (h i (L.X i)).1
      simpa [dNext, prevD, he, HomotopyCategory.quotient_obj_as] using H.comm i
  · intro f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient D c).map_surjective f
    let g : K ⟶ L :=
      { f := fun i => (e i (L.X i)).symm (f.f i)
        comm' := fun i j _ => by
          apply (h i (L.X j)).1
          simpa [he, HomotopyCategory.quotient_obj_as] using f.comm i j }
    refine ⟨(HomotopyCategory.quotient C c).map g, ?_⟩
    rw [Functor.mapHomotopyCategory_map]
    congr 1
    ext i
    exact he i (L.X i) (f.f i)

-- A map out of the unit is determined by one on the total open; restrict it to each open.
set_option backward.isDefEq.respectTransparency false in
private theorem unit_evaluation_bijective (X : RingedSpace.{u})
    (M : SheafOfModules.{u} (moduleRings X)) :
    Function.Bijective ((RingedSpace.globalSectionsFunctor X).map :
      (SheafOfModules.unit (moduleRings X) ⟶ M) →
      ((RingedSpace.globalSectionsFunctor X).obj (SheafOfModules.unit (moduleRings X)) ⟶
        (RingedSpace.globalSectionsFunctor X).obj M)) := by
  constructor
  · intro f g hfg
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    let i : op (⊤ : TopologicalSpace.Opens X) ⟶ U := (homOfLE le_top).op
    have hf := PresheafOfModules.naturality_apply f.val i (1 : (moduleRings X).obj.obj (op ⊤))
    have hg := PresheafOfModules.naturality_apply g.val i (1 : (moduleRings X).obj.obj (op ⊤))
    simp only [SheafOfModules.unit, PresheafOfModules.unit_map_one] at hf hg
    change f.val.app U (1 : (moduleRings X).obj.obj U) =
      g.val.app U (1 : (moduleRings X).obj.obj U)
    exact hf.trans ((congrArg (fun z => M.val.map i z)
      (CategoryTheory.congr_fun hfg (1 : (moduleRings X).obj.obj (op ⊤)))).trans hg.symm)
  · intro f
    let s : M.sections := M.val.sectionsMk
      (fun U => M.val.map ((homOfLE le_top).op) (f (1 : (moduleRings X).obj.obj (op ⊤)))) (by
        intro U V i
        rw [← PresheafOfModules.map_comp_apply]
        congr 1)
    refine ⟨M.unitHomEquiv.symm s, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (M.unitHomEquiv (M.unitHomEquiv.symm s)).val (op ⊤) =
      f (1 : (moduleRings X).obj.obj (op ⊤))
    rw [Equiv.apply_symm_apply]
    change M.val.map (𝟙 (op ⊤)) (f (1 : (moduleRings X).obj.obj (op ⊤))) =
      f (1 : (moduleRings X).obj.obj (op ⊤))
    simp

-- Transport the degree-zero bijection along the single-complex component isomorphism.
private theorem map_bijective_of_source_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {S U : C} (e : S ≅ U)
    (h : ∀ Y : C, Function.Bijective (F.map : (U ⟶ Y) → (F.obj U ⟶ F.obj Y)))
    (Y : C) : Function.Bijective (F.map : (S ⟶ Y) → (F.obj S ⟶ F.obj Y)) := by
  constructor
  · intro f g hfg
    have he : e.inv ≫ f = e.inv ≫ g := (h Y).1 (by simp [hfg])
    simpa using congrArg (fun k => e.hom ≫ k) he
  · intro f
    obtain ⟨g, hg⟩ := (h Y).2 (F.map e.inv ≫ f)
    refine ⟨e.hom ≫ g, ?_⟩
    simp [hg]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation at one identifies homotopy classes of maps from the structure sheaf
in degree zero with maps from the global sections ring in degree zero.
Source: Stacks Project, Tag 09M1, proof, first paragraph, and Tag 0B6A.
(blueprint: lem-pc-structure-sheaf-homotopy-global-sections).
Proof: For a complex J, a chain map from O_X[0] is an O_X-linear morphism
O_X to J^0 whose composite with d^0 is zero. Evaluate at one on the total open.
The inverse takes a global cycle z to the morphism whose value on an open U at
r is r times the restriction of z to U. Naturality and linearity give inverse
additive maps. The identical cycle z determines the A-linear chain map from
A[0] to the termwise global-sections complex. A homotopy between two maps on
either side is a degree minus one section t with d(t) equal to the difference
of the degree zero cycles. Thus evaluation and its inverse identify the
homotopy relations, and descend to inverse additive maps on the quotient.
Postcomposition with a chain map sends z to its degree zero image, so commutes
with evaluation. Every morphism in the homotopy category has a chain-map
representative; changing it by a homotopy changes none of these classes. This
proves naturality for all homotopy-category morphisms. The construction uses
only global cycles and boundaries, with no injectivity or boundedness assumption;
it applies to the empty scheme and the zero ring as well. -/
theorem structureSheaf_homotopy_globalSections (X : RingedSpace.{u}) :
    let C := SheafOfModules.{u} (moduleRings X)
    let A := (moduleRings X).obj.obj (op ⊤)
    let P := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj
        (SheafOfModules.unit (moduleRings X)))
    let Q := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))
    let G := (RingedSpace.globalSectionsFunctor X).mapHomotopyCategory
      (ComplexShape.up ℤ)
    ∃ e : ∀ J : HomotopyCategory C (ComplexShape.up ℤ),
      (P ⟶ J) ≃+ (Q ⟶ G.obj J),
      ∀ (J J' : HomotopyCategory C (ComplexShape.up ℤ)) (f : J ⟶ J') (g : P ⟶ J),
        e J' (g ≫ f) = e J g ≫ G.map f := by
  classical
  let C := SheafOfModules.{u} (moduleRings X)
  let A := (moduleRings X).obj.obj (op ⊤)
  let U := SheafOfModules.unit (moduleRings X)
  let F := RingedSpace.globalSectionsFunctor X
  let K := (CochainComplex.singleFunctor C 0).obj U
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ)
  have hK (i : ℤ) (Y : C) : Function.Bijective
      (F.map : (K.X i ⟶ Y) → (F.obj (K.X i) ⟶ F.obj Y)) := by
    by_cases hi : i = 0
    · subst i
      exact map_bijective_of_source_iso F
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 U)
        (unit_evaluation_bijective X) Y
    · have hz : IsZero (K.X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 U i hi
      have hzF := F.map_isZero hz
      refine ⟨fun f g _ => hz.eq_of_src f g, fun f => ⟨0, ?_⟩⟩
      exact hzF.eq_of_src _ _
  let b : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app U
  let a := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).mapIso b
  let e (J : HomotopyCategory C (ComplexShape.up ℤ)) :
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶ J) ≃+
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ⟶
        G.obj J) :=
    AddEquiv.ofBijective
      (AddMonoidHom.mk' (fun g => a.inv ≫ G.map g) (fun g h => by simp))
      (by
        have hG := map_homotopy_bijective F K hK J.as
        constructor
        · intro f g hfg
          apply hG.1
          have he := congrArg (fun k => a.hom ≫ k) hfg
          simpa using he
        · intro f
          obtain ⟨g, hg⟩ := hG.2 (a.hom ≫ f)
          change G.map g = a.hom ≫ f at hg
          refine ⟨g, ?_⟩
          simp [hg])
  refine ⟨e, ?_⟩
  intro J J' f g
  change a.inv ≫ G.map (g ≫ f) = (a.inv ≫ G.map g) ≫ G.map f
  simp only [Functor.map_comp, Category.assoc]

end AlgebraicGeometry
