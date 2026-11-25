/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.FinitePresentationModuleMapDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Order

/-! # Descent of bounded finitely presented module families

Source: Stacks Project, Tag 01ZR, Lemma 32.10.2, clause (1).
(blueprint: lem-pc-bounded-graded-family-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem zeroFree_isZero (X : Scheme.{u}) :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sigma.hom_ext
  intro i
  exact i.elim

private theorem zeroFree_fp (X : Scheme.{u}) :
    (SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}).IsFinitePresentation := by
  let M := SheafOfModules.free (R := X.ringCatSheaf) PEmpty.{u + 1}
  let q : M.LocalGeneratorsData :=
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf) PEmpty.{u + 1}).localGeneratorsData
  have hq : q.IsLocallyFreeData := inferInstance
  have hf : q.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite PEmpty.{u + 1}
    infer_instance
  have : M.IsFiniteLocallyFree := by
    constructor
    exact ⟨q, hq, hf⟩
  exact inferInstanceAs M.IsFinitePresentation

private noncomputable def familyTransition
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    {i : I} {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) :=
  Scheme.Modules.moduleBaseChange f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))

private noncomputable def familyLimit
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) {i : I}
    {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j) :=
  Scheme.Modules.moduleBaseChange f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))

private noncomputable def familyComparison
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) {i : I}
    {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    familyLimit R c f hij ≅ familyTransition R f hij hjk ⋙
      familyLimit R c f (hij.trans hjk) :=
  Scheme.Modules.tensorPullbackCompositionIso _ _ _ (by
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa using c.w (homOfLE hjk).op)

private theorem familyLimit_isZero
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) {i : I}
    {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j)
    (M : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules) (hM : IsZero M) :
    IsZero ((familyLimit R c f hij).obj M) := by
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction
    (baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
  have : (familyLimit R c f hij).IsLeftAdjoint := adj.isLeftAdjoint
  exact Functor.map_isZero _ hM

/-- Descent of bounded finitely presented module families.
Source: Stacks Project, Tag 01ZR, Lemma 32.10.2, clause (1).
(blueprint: lem-pc-bounded-graded-family-descent)

Proof: For each n in the finite integer interval [a,b], apply the object clause of
finitePresentation_module_map_descent to M n. Directedness gives a stage j above i and
all the finitely many stages obtained. Pull each model to j. Tensor pullback preserves
finite presentation, hence quasicoherence, and its composition isomorphism identifies
the limit pullback with M n. Define F n to be that pullback when n lies in [a,b] and
the zero module otherwise. The zero module is finitely presented and quasicoherent;
its tensor pullback is zero because tensor pullback is a left adjoint. For n outside
the interval, hM_zero identifies M n as zero too, and the unique isomorphism between
zero objects completes the family comparison. If the interval is empty, the same
construction uses a common stage above i and the zero family. The chosen index i
ensures I is nonempty even in that case. -/
theorem bounded_graded_family_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : ℤ → (pullback f (c.π.app (op i))).Modules)
    (a b : ℤ) (hM_zero : ∀ n : ℤ, n < a ∨ b < n → IsZero (M n))
    (hM_fp : ∀ n : ℤ, (M n).IsFinitePresentation)
    (hM_qc : ∀ n : ℤ, (M n).IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (F : ℤ → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (F n)) ∧
      (∀ n : ℤ, (F n).IsFinitePresentation) ∧
      (∀ n : ℤ, (F n).IsQuasicoherent) ∧
      Nonempty (∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (F n) ≅ M n) := by
  classical
  have : Nonempty I := ⟨i⟩
  have hm (n : ℤ) := (finitePresentation_module_map_descent R c hc i f).1
    (M n) (hM_fp n) (hM_qc n)
  choose j hi N hNfp hNqc e using hm
  let s := Finset.Icc a b
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (s.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (n : ℤ) (hn : n ∈ s) : j n ≤ k :=
    hk (j n) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
  let F : ℤ → (pullback f (Spec.map (R.map (homOfLE hik)))).Modules := fun n ↦
    if hn : n ∈ s then (familyTransition R f (hi n) (hjk n hn)).obj (N n)
    else SheafOfModules.free (R :=
      (pullback f (Spec.map (R.map (homOfLE hik)))).ringCatSheaf) PEmpty.{u + 1}
  have hFfp (n : ℤ) : (F n).IsFinitePresentation := by
    dsimp only [F]
    split_ifs with hn
    · have := hNfp n
      exact Scheme.Modules.isFinitePresentation_tensorPullback _ _
    · exact zeroFree_fp _
  refine ⟨k, hik, F, ?_, hFfp, ?_, ⟨?_⟩⟩
  · intro n hn
    have hs : n ∉ s := by simp only [s, Finset.mem_Icc]; omega
    dsimp only [F]
    rw [dite_eq_right hs]
    exact zeroFree_isZero _
  · intro n
    have := hFfp n
    infer_instance
  · intro n
    dsimp only [F]
    split_ifs with hn
    · exact ((familyComparison R c f (hi n) (hjk n hn)).symm.app (N n)) ≪≫
        (e n).some
    · have hz := familyLimit_isZero R c f hik _ (zeroFree_isZero _)
      exact hz.iso (hM_zero n (by simp only [s, Finset.mem_Icc] at hn; omega))
end AlgebraicGeometry
