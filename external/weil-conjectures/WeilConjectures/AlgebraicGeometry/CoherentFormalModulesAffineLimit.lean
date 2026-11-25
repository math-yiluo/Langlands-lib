/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAffineSectionsAdic
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerCompletedScalarLimit
import WeilConjectures.Algebra.Category.ModuleCat.AdicTowerFiniteLimit
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # CoherentFormalModulesAffineLimit

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Construction of the finite completed-module limit functor, with its projections.
This asserts no equivalence and constructs no inverse functor.

Source: Stacks Project, Cohomology of Schemes, Lemma 087W, proof paragraphs on
Nakayama, the surjective kernel tower and Mittag-Leffler; Schemes 01I7/01IB.
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-limit).

Proof: For each F, apply coherent/finite-type correspondence on Spec A and the affine
sections formula for ideal products and cokernels. Its sections M_n are finite A-modules,
annihilated by I^(n+1), with surjective transitions whose kernels are I^(n+1)M_(n+1).
Form the ModuleCat limit of this tower. Each coordinate is an A/I^(n+1)-module;
act on compatible sequences by the coordinates of a completed scalar. This preserves
compatibility and satisfies the module laws coordinatewise. The underlying A-module
is the original limit, since restricted completed scalars act by their residues.
Surjectivity of tower projections allows lifts x_i of generators at level one. Their
coordinate maps (A/I^(n+1))^t -> M_n are surjective by nilpotent Nakayama. The kernels
have surjective transitions: lift a kernel vector, then subtract an element in
I^(n+1) times the free module to kill its next coordinate image. Mittag-Leffler gives
a surjection from the completed free module onto the limit, so it is finite.
For fixed n, a vector lifting a limit element with zero nth coordinate has nth
coordinate in the kernel tower. Lift that vector through the kernel limit and subtract
it. The difference belongs to I^(n+1) times the completed free module, by the completion
quotient formula. Thus the projection kernel is exactly I^(n+1) times the limit.
A morphism of formal systems induces an A-linear map of limits; the coordinatewise
scalar action makes it completion-linear. Uniqueness in the limit proves identity and
composition, giving L into the full finite-module subcategory. The limit cone supplies
p and its IsLimit witness. Its map equation gives naturality; the kernel calculation
gives the third assertion; componentwise scalar action gives the last assertion. -/
theorem coherentFormalModules_affine_limit (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) :
    ∃ L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
      ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N),
    ∃ p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A),
    (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))) ∧
    (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ),
      Function.Surjective ((p F).app (op n)) ∧
      LinearMap.ker ((p F).app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A
          ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
            (L.obj F).obj))) ∧
    (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (L.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x) := by
  classical
  let C := CoherentFormalModule (Spec (CommRingCat.of A)) J
  let S := ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))
  let T : C ⥤ (ℕᵒᵖ ⥤ ModuleCat.{u} A) :=
    ObjectProperty.ι _ ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Spec (CommRingCat.of A)).Modules (ModuleCat.{u} A)).obj
        (moduleSpecΓFunctor (R := CommRingCat.of A))
  have ht (F : C) := coherentFormalModule_affine_sections_adic A I J hJ F
  choose N e hs using fun F : C ↦
    ModuleCat.adicTower_completedScalarLimit A I (T.obj F) (ht F).2.1
  have hn (F : C) := ModuleCat.adicTower_finiteLimit A I (T.obj F)
    (ht F).1 (ht F).2.1 (ht F).2.2 (N F) (e F) (hs F)
  let p (F : C) := ((limit.cone (T.obj F)).extend (e F).hom).π
  let u {F G : C} (f : F ⟶ G) : S.obj (N F) ⟶ S.obj (N G) :=
    (e F).hom ≫ lim.map (T.map f) ≫ (e G).inv
  have hu {F G : C} (f : F ⟶ G) (n : ℕ) :
      u f ≫ (p G).app (op n) = (p F).app (op n) ≫ (T.map f).app (op n) := by
    simp [u, p, Category.assoc]
  have hlinear {F G : C} (f : F ⟶ G) (r : AdicCompletion I A) (x : N F) :
      u f (r • x) = r • u f x := by
    apply (ModuleCat.mono_iff_injective (e G).hom).mp inferInstance
    apply Concrete.limit_ext (T.obj G)
    intro j
    obtain ⟨n⟩ := j
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) r)
    have hF := hs F n r a x ha.symm
    have hG := hs G n r a (u f x) ha.symm
    change (p G).app (op n) (u f (r • x)) =
      (p G).app (op n) (r • u f x)
    change (p F).app (op n) (r • x) = a • (p F).app (op n) x at hF
    change (p G).app (op n) (r • u f x) = a • (p G).app (op n) (u f x) at hG
    rw [hG]
    have huf (y : N F) :
        (p G).app (op n) (u f y) = (T.map f).app (op n) ((p F).app (op n) y) :=
      congrArg (fun k ↦ k y) (hu f n)
    rw [huf, hF, map_smul, huf]
  let m {F G : C} (f : F ⟶ G) : N F ⟶ N G := ModuleCat.ofHom
    { toFun := u f
      map_add' := map_add (u f).hom
      map_smul' := hlinear f }
  have hm {F G : C} (f : F ⟶ G) : S.map (m f) = u f := by
    ext x
    rfl
  let L₀ : C ⥤ ModuleCat.{u} (AdicCompletion I A) :=
    { obj := N
      map := m
      map_id F := by
        apply S.map_injective
        rw [hm, S.map_id]
        dsimp only [u]
        rw [T.map_id, lim.map_id]
        simp
      map_comp f g := by
        apply S.map_injective
        rw [S.map_comp, hm, hm, hm]
        dsimp only [u]
        rw [T.map_comp, lim.map_comp]
        simp [Category.assoc] }
  let L := ObjectProperty.lift
    (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)
    L₀ (fun F ↦ (hn F).1)
  refine ⟨L, p, ?_, ?_, ?_, ?_⟩
  · intro F
    exact ⟨(limit.isLimit (T.obj F)).extendIso (e F).hom⟩
  · intro F G f n
    change S.map (m f) ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (T.map f).app (op n)
    rw [hm]
    exact hu f n
  · intro F n
    exact (hn F).2 n
  · intro F n r a x ha
    exact hs F n r a x ha

end AlgebraicGeometry
