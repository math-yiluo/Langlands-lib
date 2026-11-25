/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

private lemma localCycleLift_differential_apply (X : Scheme.{u})
    {A A' B B' C D : X.Modules} (d : C ⟶ D) (a : A ⟶ A') (b : B ⟶ B')
    (p : C ⟶ SheafOfModules.homObj (R := X.sheaf) A B)
    (q : C ⟶ SheafOfModules.homObj (R := X.sheaf) A' B')
    (r : D ⟶ SheafOfModules.homObj (R := X.sheaf) A B') (c : ℤˣ)
    (h : d ≫ r = p ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 A) b -
      c • (q ≫ SheafOfModules.homObjMap (R := X.sheaf) a (𝟙 B')))
    (U : X.Opens) (s : C.val.obj (op U)) (z : A.val.obj (op U))
    (hs : d.val.app (op U) s = 0) (hz : a.val.app (op U) z = 0) :
    b.val.app (op U) ((p.val.app (op U) s).app (op (Over.mk (𝟙 U))) z) = 0 := by
  let ev : (SheafOfModules.homObj (R := X.sheaf) A B').val.obj (op U) →+
      B'.val.obj (op U) :=
    { toFun f := f.app (op (Over.mk (𝟙 U))) z
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have he := congrArg (fun k : C ⟶ SheafOfModules.homObj (R := X.sheaf) A B' ↦
    ev ((F.map k).hom s)) h
  rw [Functor.map_sub] at he
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    map_sub, map_zsmul] at he
  change (r.val.app (op U) (d.val.app (op U) s)).app (op (Over.mk (𝟙 U))) z =
    b.val.app (op U) ((p.val.app (op U) s).app (op (Over.mk (𝟙 U))) z) -
      (c : ℤ) • (show B'.val.obj (op U) from
        (q.val.app (op U) s).app (op (Over.mk (𝟙 U))) (a.val.app (op U) z)) at he
  rw [hs, hz, map_zero, map_zero] at he
  change 0 = b.val.app (op U) ((p.val.app (op U) s).app (op (Over.mk (𝟙 U))) z) -
    (c : ℤ) • (0 : B'.val.obj (op U)) at he
  simpa only [smul_zero, sub_zero] using he.symm

set_option backward.isDefEq.respectTransparency false in
-- The differential formula unfolds localized Hom and evaluated kernel structures.
/-- Every pair of local cycle representatives has a representative in the target cycles.
Source: Stacks Project, Tag 0A8X, Hom differential formula.
(blueprint: new-b2-homology-evaluation-local-cycle-lift).

Apply the differential projection formula in degree n to the Hom cocycle, at source
index -n and target index 1. Evaluation on the given T-cycle kills the precomposition
term, while the Hom cycle equation kills the differential term. Thus the evaluation
in J-degree zero has differential zero. Evaluation of sheaves of modules at U preserves
kernels. Applying this to the cycle inclusion identifies its image with the kernel
of the evaluated J-differential, and supplies the required b. The argument also works
on the empty open and when either cycle representative is zero.
-/
theorem homologyEvaluation_local_cycle_lift (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    ∀ (U : X.Opens)
      (φ : ((homComplex (R := X.sheaf) T J).cycles n).val.obj (op U))
      (z : (T.cycles (-n)).val.obj (op U)),
      ∃ b : (J.cycles 0).val.obj (op U),
        (J.iCycles 0).val.app (op U) b =
          ((homologyEvaluationProjection X T J n).val.app (op U)
            (((homComplex (R := X.sheaf) T J).iCycles n).val.app (op U) φ)).app
              (op (Over.mk (𝟙 U)))
            (((T.iCycles (-n)).val.app (op U)) z) := by
  intro U φ z
  let P := homComplex (R := X.sheaf) T J
  let π := Classical.choose (homComplex_projections_exists (R := X.sheaf))
  let x := ((π T J n (-n) 0 (by omega)).val.app (op U)
    ((P.iCycles n).val.app (op U) φ)).app
      (op (Over.mk (𝟙 U))) ((T.iCycles (-n)).val.app (op U) z)
  have hformula := (Classical.choose_spec
    (homComplex_projections_exists (R := X.sheaf))).2.1
    T J n (n + 1) (-n) 1 0 (1 - n) rfl (by omega) (by omega) (by omega)
  have hP : (P.d n (n + 1)).val.app (op U)
      ((P.iCycles n).val.app (op U) φ) = 0 :=
    congrArg (fun k ↦ k.val.app (op U) φ) (P.iCycles_d n (n + 1))
  have hT : (T.d (-n) (1 - n)).val.app (op U)
      ((T.iCycles (-n)).val.app (op U) z) = 0 :=
    congrArg (fun k ↦ k.val.app (op U) z) (T.iCycles_d (-n) (1 - n))
  have hd : (J.d 0 1).val.app (op U) x = 0 :=
    localCycleLift_differential_apply X (P.d n (n + 1)) (T.d (-n) (1 - n))
      (J.d 0 1) (π T J n (-n) 0 (by omega)) (π T J n (1 - n) 1 (by omega))
      (π T J (n + 1) (-n) 1 (by omega)) n.negOnePow hformula U
      ((P.iCycles n).val.app (op U) φ) ((T.iCycles (-n)).val.app (op U) z) hP hT
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let S := ShortComplex.mk (E.map (J.iCycles 0)) (E.map (J.d 0 1))
    (by rw [← E.map_comp, J.iCycles_d, E.map_zero])
  have hk : IsLimit (KernelFork.ofι S.f S.zero) :=
    isLimitForkMapOfIsLimit' E _ (J.cyclesIsKernel 0 1 (by simp :
      (ComplexShape.up ℤ).next 0 = 1))
  have hs : S.Exact := S.exact_of_f_is_kernel hk
  exact (S.moduleCat_exact_iff.mp hs) x hd

end CategoryTheory
