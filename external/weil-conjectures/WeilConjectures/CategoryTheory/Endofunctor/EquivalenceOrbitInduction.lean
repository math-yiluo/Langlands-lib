/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact orbit induction for an additive autoequivalence

Source: steps 7--8 of the twisted ringed-action-site construction, motivated by
Stacks Tag 00W0 (blueprint: lem-sf-equivalence-orbit-induction).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] (F : A ⥤ A) [F.IsEquivalence]

private noncomputable def orbitFunctor : ℤ → A ⥤ A
  | .ofNat n => F.iterate n
  | .negSucc n => F.inv.iterate (n + 1)

omit [F.IsEquivalence] in
private theorem posObj_eq (X : A) (n : ℕ) :
    Free.posObj F X n = (F.iterate n).obj X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Free.posObj, ih, Functor.iterate_succ, Functor.comp_obj]

private theorem negObj_eq (X : A) (n : ℕ) :
    Free.negObj F X n = (F.inv.iterate (n + 1)).obj X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Free.negObj, ih, Functor.iterate_succ, Functor.comp_obj]

private theorem powNat_functor (e : A ≌ A) (n : ℕ) :
    (e.powNat n).functor = e.functor.iterate n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih' =>
    change e.functor ⋙ (e.powNat (n + 1)).functor = _
    rw [ih']
    simpa only [Functor.iterate_one, Nat.add_comm 1] using
      (e.functor.iterate_add 1 (n + 1)).symm

private theorem powerFunctor_eq (n : ℤ) :
    (F.asEquivalence ^ n).functor = orbitFunctor F n := by
  cases n with
  | ofNat n => exact powNat_functor F.asEquivalence n
  | negSucc n => exact powNat_functor F.asEquivalence.symm (n + 1)

private theorem obj_eq (X : A) (n : ℤ) :
    (orbitFunctor F n).obj X = Free.obj F X n := by
  cases n with
  | ofNat n => exact (posObj_eq F X n).symm
  | negSucc n => exact (negObj_eq F X n).symm

omit [F.IsEquivalence] in
private theorem posMap_eq {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    Free.posMap F f n =
      eqToHom (posObj_eq F X n) ≫ (F.iterate n).map f ≫
        eqToHom (posObj_eq F Y n).symm := by
  induction n with
  | zero => simp [Free.posMap, Functor.iterate_zero]
  | succ n ih =>
    simpa only [Free.posMap, Functor.iterate_succ, Functor.comp_map,
      Functor.map_comp, eqToHom_map] using congrArg F.map ih

private theorem negMap_eq {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    Free.negMap F f n =
      eqToHom (negObj_eq F X n) ≫ (F.inv.iterate (n + 1)).map f ≫
        eqToHom (negObj_eq F Y n).symm := by
  induction n with
  | zero => simp [Free.negMap, Functor.iterate_one]
  | succ n ih =>
    simpa only [Free.negMap, Functor.iterate_succ, Functor.comp_map,
      Functor.map_comp, eqToHom_map] using congrArg F.inv.map ih

private theorem objMap_eq {X Y : A} (f : X ⟶ Y) (n : ℤ) :
    Free.objMap F f n =
      eqToHom (obj_eq F X n).symm ≫ (orbitFunctor F n).map f ≫
        eqToHom (obj_eq F Y n) := by
  cases n with
  | ofNat n => exact posMap_eq F f n
  | negSucc n => exact negMap_eq F f n

private noncomputable def orbitStep (n : ℤ) :
    orbitFunctor F n ⋙ F ≅ orbitFunctor F (n + 1) :=
  NatIso.ofComponents
    (fun X ↦ F.mapIso (eqToIso (obj_eq F X n)) ≪≫ Free.objSucc F X n ≪≫
      (eqToIso (obj_eq F X (n + 1))).symm)
    (by
      intro X Y f
      have h := Free.map_objMap_comp_objSucc (F := F) f n
      rw [objMap_eq, objMap_eq] at h
      have hh := congrArg (fun z ↦ F.map (eqToHom (obj_eq F X n)) ≫ z ≫
        eqToHom (obj_eq F Y (n + 1)).symm) h
      simp only [Functor.map_comp, Category.assoc] at hh
      simpa only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
        Iso.symm_hom, eqToIso.inv, Category.assoc, ← F.map_comp_assoc,
        eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
        F.map_id, Category.id_comp, Category.comp_id] using hh)

private noncomputable def powerStep (n : ℤ) :
    (F.asEquivalence ^ n).functor ⋙ F ≅ (F.asEquivalence ^ (n + 1)).functor :=
  isoWhiskerRight (eqToIso (powerFunctor_eq F n)) F ≪≫ orbitStep F n ≪≫
    (eqToIso (powerFunctor_eq F (n + 1))).symm

private noncomputable def powerSum [HasCoproducts.{0} A] (X : A) :
    ∐ (fun n : ℤ ↦ (F.asEquivalence ^ n).functor.obj X) ≅
      ((Free.functor F).obj X).carrier :=
  Sigma.mapIso (fun n ↦
    eqToIso ((congrArg (fun G : A ⥤ A ↦ G.obj X) (powerFunctor_eq F n)).trans
      (obj_eq F X n)))

/-- The normalizations of exact orbit induction for an additive autoequivalence.
Source: steps 7--8 of the twisted ringed-action-site construction
(blueprint: lem-sf-equivalence-orbit-induction). -/
structure ExactOrbitInduction [Abelian A] [F.Additive] where
  /-- The free fixed-pair functor. -/
  induction : A ⥤ IsoAlgebra F
  /-- Its adjunction to forgetting. -/
  adjunction : induction ⊣ forget F
  /-- The underlying integer orbit sum. -/
  sum [HasCoproducts.{0} A] (X : A) :
    ∐ (fun n : ℤ ↦ (F.asEquivalence ^ n).functor.obj X) ≅
      (induction.obj X).carrier
  /-- The canonical one-step power comparison. -/
  step (n : ℤ) :
    (F.asEquivalence ^ n).functor ⋙ F ≅ (F.asEquivalence ^ (n + 1)).functor
  /-- Induction shifts the n-th summand to the (n+1)-st. -/
  shift [HasCoproducts.{0} A] (X : A) (n : ℤ) :
    F.map (Sigma.ι (fun k : ℤ ↦ (F.asEquivalence ^ k).functor.obj X) n ≫
      (sum X).hom) ≫ (induction.obj X).obj.str =
    (step n).hom.app X ≫
      Sigma.ι (fun k : ℤ ↦ (F.asEquivalence ^ k).functor.obj X) (n + 1) ≫ (sum X).hom
  /-- The hom-equivalence is restriction to the zeroth summand. -/
  zero [HasCoproducts.{0} A] (X : A) (N : IsoAlgebra F) (f : induction.obj X ⟶ N) :
    adjunction.homEquiv X N f =
      Sigma.ι (fun k : ℤ ↦ (F.asEquivalence ^ k).functor.obj X) 0 ≫ (sum X).hom ≫ f.hom.f
  /-- Additivity on the actual underlying morphisms. -/
  add {X Y : A} (f g : X ⟶ Y) :
    (induction.map (f + g)).hom.f = (induction.map f).hom.f + (induction.map g).hom.f
  /-- Left exactness. -/
  limits : PreservesFiniteLimits induction
  /-- Right exactness. -/
  colimits : PreservesFiniteColimits induction

/-- Orbit-sum induction is additive and exact, with the specified power and zero-summand
normalizations. Source: steps 7--8 of the twisted action-site construction; AB5 implies AB4.
(blueprint: lem-sf-equivalence-orbit-induction).

Proof: use the source library's explicit free algebra, whose sum is indexed by all integers.
Identify its recursively defined iterates with the powers of the chosen autoequivalence.
Conjugate its successor comparisons by those identifications. The source shift formula
then gives the displayed shift equation, and the free adjunction is restriction at zero.
The same restriction proves additivity. Coproducts preserve monomorphisms by AB4, and each
iterate preserves them because it is an equivalence. Thus the free functor preserves
monomorphisms. Its adjunction preserves cokernels; in abelian categories these two facts
imply preservation of homology and hence all finite limits. The adjunction also supplies
all finite colimits. The proof applies to the zero category and empty input objects as well.
-/
theorem exists_exactOrbitInduction [Abelian A] [F.Additive]
    [IsGrothendieckAbelian.{v} A] : Nonempty (ExactOrbitInduction F) := by
  classical
  have : (Free.functor F).IsLeftAdjoint := (Free.adjunction F).isLeftAdjoint
  have : (Free.functor F).Additive := by
    refine ⟨fun {X Y} f g ↦ Free.hom_ext ?_⟩
    change Sigma.ι (Free.obj F X) 0 ≫ (Free.map (f + g)).hom.f =
      Sigma.ι (Free.obj F X) 0 ≫ ((Free.map f).hom.f + (Free.map g).hom.f)
    simp [Free.map_hom_f, Preadditive.comp_add, Sigma.ι_map]
  have : (MorphismProperty.monomorphisms A).IsStableUnderCoproductsOfShape ℤ := by
    infer_instance
  have : (Free.functor F).PreservesMonomorphisms := inferInstance
  have : (Free.functor F).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels (Free.functor F)
  refine ⟨{
    induction := Free.functor F
    adjunction := Free.adjunction F
    sum := powerSum F
    step := powerStep F
    shift := ?_
    zero := ?_
    add := ?_
    limits := Functor.preservesFiniteLimits_of_preservesHomology _
    colimits := inferInstance }⟩
  · intro _ X n
    simp only [powerSum, Functor.map_comp, Category.assoc, Sigma.ι_mapIso_hom,
      powerStep, orbitStep, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, Functor.whiskerRight_app, eqToIso.hom, Iso.symm_hom,
      NatIso.ofComponents_hom_app, Functor.mapIso_hom, eqToIso.inv]
    simp only [eqToHom_app, ← F.map_comp_assoc, eqToHom_trans,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change _ ≫ (Free.str F X).hom = _
    simp only [F.map_comp, Category.assoc, Free.map_ι_comp_str]
  · intro _ X N f
    simp only [Free.adjunction, Adjunction.mkOfHomEquiv_homEquiv]
    change Sigma.ι (Free.obj F X) 0 ≫ f.hom.f = _
    simp [powerSum]
  · intro X Y f g
    exact (Free.functor F ⋙ forget F).map_add (f := f) (g := g)

end CategoryTheory.Endofunctor.IsoAlgebra
