/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem pi_kernel {C : Type*} [Category C] [HasZeroMorphisms C]
    {J : Type*} {A B E : J → C} [HasProduct A] [HasProduct B] [HasProduct E]
    (f : ∀ j, A j ⟶ B j) (g : ∀ j, B j ⟶ E j) (w : ∀ j, f j ≫ g j = 0)
    (h : ∀ j, Nonempty (IsLimit (KernelFork.ofι (f j) (w j)))) :
    Nonempty (IsLimit (KernelFork.ofι (Limits.Pi.map f) (by
      apply Pi.hom_ext
      intro j
      simp [w]) :
      KernelFork (Limits.Pi.map g))) := by
  classical
  let H j := (h j).some
  refine ⟨KernelFork.IsLimit.ofι _ _
    (fun {_} k hk ↦ Pi.lift fun j ↦
      (H j).lift (KernelFork.ofι (k ≫ Pi.π B j) (by
        have := congrArg (fun q ↦ q ≫ Pi.π E j) hk
        simpa only [Category.assoc, Limits.Pi.map_π, zero_comp] using this))) ?_ ?_⟩
  · intro W k hk
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc]
    exact (H j).fac _ WalkingParallelPair.zero
  · intro W k hk m hm
    apply Pi.hom_ext
    intro j
    apply Fork.IsLimit.hom_ext (H j)
    have := congrArg (fun q ↦ q ≫ Pi.π B j) hm
    simp only [Pi.lift_comp_π]
    rw [Fork.IsLimit.lift_ι]
    simpa only [Category.assoc, Limits.Pi.map_π, KernelFork.ι_ofι]
      using this

set_option backward.isDefEq.respectTransparency false in
/-- The resolution augmentation identifies Cech cochains with degree-zero column homology.
Source: Stacks Project, Tag 01EQ, the beta construction; Tag 01DZ, left exactness of sections.
(blueprint: lem-sc-module-cech-resolution-column-zero)

Proof: the resolution augmentation identifies F with the kernel of I^0 → I^1.
For each finite intersection, sections preserve this kernel, since sections are left exact.
Restriction of scalars preserves the underlying kernel. Taking the product over tuples
also preserves kernels: a tuple lies in the kernel exactly when every coordinate does.
There are no incoming boundaries in degree zero. Thus the product augmentation identifies
Cech n-cochains of F with the zeroth homology of the column. The source is concentrated
in degree zero and its zeroth homology is itself; the induced map is this identification.
The choice of the chain-map proof ha has no effect, by proof irrelevance. This argument
requires no positive-degree vanishing assumption. -/
theorem moduleCech_resolution_column_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (I : InjectiveResolution F)
    (ha : (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (I.ι.f 0).val) ≫ (moduleCechDouble U I).d 0 1 = 0)
    (n : ℕ) :
    let A := (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat
    let a : A ⟶ (moduleCechDouble U I).X 0 :=
      (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (I.ι.f 0).val)
    QuasiIsoAt
      ((CochainComplex.fromSingle₀Equiv ((moduleCechDouble U I).flip.X n)
        (A.X n)).symm
        ⟨a.f n, by simpa [a, A, moduleCechDouble] using congrArg (fun f ↦ f.f n) ha⟩) 0 := by
  dsimp
  rw [CochainComplex.quasiIsoAt₀_iff]
  rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)]
  rw [ShortComplex.exact_and_mono_f_iff_f_is_kernel]
  simp only [HomologicalComplex.shortComplexFunctor'_map_τ₂,
    CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  let G (y : Fin (n + 1) → ι) :=
    SheafOfModules.evaluation X.ringCatSheaf (op (∏ᶜ fun l ↦ U (y l))) ⋙
      ModuleCat.restrictScalars
        (X.ringCatSheaf.obj.map
          (isTerminalTop.op.to (op (∏ᶜ fun l ↦ U (y l))))).hom
  have (y : Fin (n + 1) → ι) : (G y).Additive := by
    dsimp [G, SheafOfModules.evaluation]
    infer_instance
  have (y : Fin (n + 1) → ι) : PreservesFiniteLimits (G y) := by
    dsimp [G]
    infer_instance
  have h (y : Fin (n + 1) → ι) :
      Nonempty (IsLimit (KernelFork.ofι ((G y).map (I.ι.f 0))
        (by
          rw [← (G y).map_comp, I.ι_f_zero_comp_complex_d, (G y).map_zero]) :
        KernelFork ((G y).map (I.cocomplex.d 0 1)))) :=
    ⟨KernelFork.mapIsLimit _ I.isLimitKernelFork (G y)⟩
  exact pi_kernel (fun y ↦ (G y).map (I.ι.f 0))
    (fun y ↦ (G y).map (I.cocomplex.d 0 1))
    (fun y ↦ by
      rw [← (G y).map_comp, I.ι_f_zero_comp_complex_d, (G y).map_zero]) h

end AlgebraicGeometry.Scheme.Modules
