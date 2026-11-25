/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.AdicCompletion.Algebra

import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import all WeilConjectures.AlgebraicGeometry.CoherentAffineMapSupportRadical

/-! # Lifting section isomorphisms over an adic completion

Source: Stacks Project, Tags 087W, 00MA, 05GG and 01I6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

private theorem completion_smul_mem
    {B : Type u} [CommRing B] (I : Ideal B)
    {M : Type u} [AddCommGroup M] [Module (AdicCompletion I B) M]
    [Module B M] [IsScalarTower B (AdicCompletion I B) M]
    (n : ℕ) (r : AdicCompletion I B)
    (hr : r ∈ I ^ n • (⊤ : Submodule B (AdicCompletion I B))) (x : M) :
    r • x ∈ I ^ n • (⊤ : Submodule B M) := by
  refine Submodule.smul_induction_on hr ?_ ?_
  · intro a ha y _
    rw [smul_assoc]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro y z hy hz
    rw [add_smul]
    exact Submodule.add_mem _ hy hz

private theorem completion_linear_map_smul
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG)
    {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module (AdicCompletion I B) M] [Module (AdicCompletion I B) N]
    [Module B M] [Module B N]
    [IsScalarTower B (AdicCompletion I B) M]
    [IsScalarTower B (AdicCompletion I B) N] [IsHausdorff I N]
    (f : M →ₗ[B] N) (r : AdicCompletion I B) (x : M) :
    f (r • x) = r • f x := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  let a : B := (r.val n).out
  have hr : r - algebraMap B (AdicCompletion I B) a ∈
      I ^ n • (⊤ : Submodule B (AdicCompletion I B)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub]
    simp only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, AdicCompletion.eval_apply]
    exact sub_eq_zero.mpr (Submodule.Quotient.mk_out (r.val n)).symm
  have hfil : ∀ y ∈ I ^ n • (⊤ : Submodule B M),
      f y ∈ I ^ n • (⊤ : Submodule B N) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro b hb z _
      rw [f.map_smul]
      exact Submodule.smul_mem_smul hb Submodule.mem_top
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  have hM : r • x - a • x ∈ I ^ n • (⊤ : Submodule B M) := by
    simpa only [sub_smul, algebraMap_smul] using completion_smul_mem I n _ hr x
  have hN : r • f x - a • f x ∈ I ^ n • (⊤ : Submodule B N) := by
    simpa only [sub_smul, algebraMap_smul] using completion_smul_mem I n _ hr (f x)
  have h₁ : f (r • x) ≡ a • f x [SMOD (I ^ n • (⊤ : Submodule B N))] := by
    rw [SModEq.sub_mem]
    simpa only [map_sub, map_smul] using hfil _ hM
  exact h₁.trans (SModEq.sub_mem.mpr hN).symm

set_option backward.isDefEq.respectTransparency false in
/-- A B-linear section isomorphism between coherent modules over the completion
of a Noetherian ring B lifts to a sheaf isomorphism with exactly those sections.

Source: Stacks Project, Tag 087W (finite formal modules), Tag 00MA (completion
of finite modules over Noetherian rings), Tag 05GG (completion modulo powers),
and Tag 01I6 (the affine quasi-coherent module equivalence).
(blueprint: lem-weil-pbc-completed-affine-coherent-iso-lift)

Proof: Put R equal to the I-adic completion of B. R is Noetherian and complete
for IR, and the section modules of coherent sheaves on Spec R are finite.
Their I-adic filtrations as B-modules agree with their IR-adic filtrations as
R-modules: (IR)^n is generated over R by the images of the finitely generated
ideal I^n, so every generator acting on a module is already a B-ideal multiple
of another module element. A B-linear map therefore preserves this filtration.
For r in R and each n choose a in B representing r modulo (IR)^n. For every x,
f(r*x)-r*f(x) lies in (IR)^n times the target, using B-linearity and filtration
preservation. Finite modules over R are complete and separated, so intersection
of these powers is zero. Hence f is R-linear. Apply the same argument to the
inverse B-linear map. These maps are inverse R-linear maps. Full faithfulness
of the affine quasi-coherent/sections equivalence lifts them to inverse sheaf
maps. Their section maps are the given ones by the counit identities.
For I=B the completion and both section modules are zero; for I=0 this is the
ordinary affine equivalence. No proper-ideal hypothesis is used. -/
theorem completedAffine_coherent_iso_lift
    (B : Type u) [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    (A D : CoherentModules (Spec (CommRingCat.of (AdicCompletion I B))))
    (e : (ModuleCat.restrictScalars (algebraMap B (AdicCompletion I B))).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of (AdicCompletion I B))).obj A.obj) ≅
      (ModuleCat.restrictScalars (algebraMap B (AdicCompletion I B))).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of (AdicCompletion I B))).obj D.obj)) :
    ∃ a : A.obj ≅ D.obj,
      (ModuleCat.restrictScalars (algebraMap B (AdicCompletion I B))).map
        ((moduleSpecΓFunctor (R := CommRingCat.of (AdicCompletion I B))).map a.hom) =
          e.hom  := by
  classical
  let R := AdicCompletion I B
  let S := ModuleCat.restrictScalars (algebraMap B R)
  let T : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R :=
    moduleSpecΓFunctor (R := CommRingCat.of R)
  let M := T.obj A.obj
  let N := T.obj D.obj
  let : Module B M := Module.compHom M (algebraMap B R)
  let : Module B N := Module.compHom N (algebraMap B R)
  have : IsScalarTower B R M := ⟨fun a r x ↦ by
    change (algebraMap B R a * r) • x = algebraMap B R a • (r • x)
    exact mul_smul _ _ _⟩
  have : IsScalarTower B R N := ⟨fun a r x ↦ by
    change (algebraMap B R a * r) • x = algebraMap B R a • (r • x)
    exact mul_smul _ _ _⟩
  have hI : I.FG := IsNoetherian.noetherian I
  have : IsNoetherianRing R := AdicCompletion.isNoetherianRing I
  have : IsAdicComplete I R := AdicCompletion.isAdicComplete hI
  have : IsAdicComplete (I.map (algebraMap B R)) R :=
    (IsAdicComplete.map_algebraMap_iff I (S := R) (M := R)).mpr inferInstance
  have : Module.Finite R N := finite_spec_sections R D
  have : IsAdicComplete (I.map (algebraMap B R)) N :=
    finite_module_complete_over_complete_noetherian R _ N
  have : IsAdicComplete I N :=
    (IsAdicComplete.map_algebraMap_iff I (S := R) (M := N)).mp inferInstance
  let f : M →ₗ[B] N := e.hom.hom
  let v : M →ₗ[R] N :=
    { toFun := fun x ↦ f x
      map_add' := f.map_add
      map_smul' := completion_linear_map_smul I hI f }
  let w : M ⟶ N := ModuleCat.ofHom (X := M) (Y := N) v
  have hw : S.map w = e.hom := by
    ext x
    rfl
  have : IsIso w := by
    have : IsIso (S.map w) := hw ▸ inferInstance
    exact isIso_of_reflects_iso w S
  have hA : A.obj.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp A.property |>.1
  have hD : D.obj.IsQuasicoherent :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType _ _).mp D.property |>.1
  let C := SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf
  let A' : C.FullSubcategory := ⟨A.obj, hA⟩
  let D' : C.FullSubcategory := ⟨D.obj, hD⟩
  let E := tildeEquiv (R := CommRingCat.of R)
  let a' : A' ≅ D' := E.inverse.preimageIso (asIso w)
  let a : A.obj ≅ D.obj := (ObjectProperty.ι
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf)).mapIso a'
  refine ⟨a, ?_⟩
  change S.map (E.inverse.map a'.hom) = e.hom
  dsimp only [a', Functor.preimageIso]
  rw [Functor.map_preimage]
  exact hw

end AlgebraicGeometry
