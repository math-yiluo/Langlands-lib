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
import Mathlib.Data.Int.Interval

/-! # Descent of maps between fixed bounded module families

Source: Stacks Project, Tag 01ZR, Lemma 32.10.2, clause (2).
(blueprint: lem-pc-bounded-graded-map-compatibility)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

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

/-- Descent of maps between fixed bounded module families.
Source: Stacks Project, Tag 01ZR, Lemma 32.10.2, clause (2).
(blueprint: lem-pc-bounded-graded-map-compatibility)

Proof: First use finite-set induction to descend any finite set of successive maps
between the limit pullbacks of the fixed family F. For the empty set take stage j,
family F, zero maps, and identity comparisons. In the induction step let G, δ and t
be the current family, maps and comparisons. Transport the new φ n to
(t n).hom ≫ φ n ≫ (t (n+1)).inv. Apply the map clause of
finitePresentation_module_map_descent to descend this map after enlarging the stage.
Let T be transition pullback and e the comparison from the current limit pullback
to T followed by the new limit pullback. Set H m = T.obj (G m). In the new degree
use the descended map; in every other degree use T.map (δ m). Define the new term
comparison as e.inv.app (G m) followed by (t m).hom. The map clause's equation,
multiplied by the two inverse comparisons, proves commutativity in the new degree.
Naturality of e.inv preserves all the equations in the previously processed degrees.
The new family remains zero outside [a,b], since T is left adjoint and preserves zero
objects; tensor pullback preserves finite presentation and hence quasicoherence.
Apply this induction to the finite interval [a,b-1]. For every remaining degree,
either n<a or b<n+1. In the first case the limit pullback of G n is zero and all
maps with this source coincide. In the second case the limit pullback of F(n+1)
is zero and all maps with this target coincide. These facts give the boundary
comparisons, including empty or singleton intervals. No square-zero equation or
canonical associativity coherence for multiple transition steps is required. -/
theorem bounded_graded_map_compatibility
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (a b : ℤ) (j : I) (hij : i ≤ j)
    (F : ℤ → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF_zero : ∀ n : ℤ, n < a ∨ b < n → IsZero (F n))
    (hF_fp : ∀ n : ℤ, (F n).IsFinitePresentation)
    (hF_qc : ∀ n : ℤ, (F n).IsQuasicoherent)
    (φ : ∀ n : ℤ, (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (F n) ⟶
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (F (n + 1))) :
    ∃ (k : I) (_hjk : j ≤ k) (hik : i ≤ k)
      (G : ℤ → (pullback f (Spec.map (R.map (homOfLE hik)))).Modules)
      (δ : ∀ n : ℤ, G n ⟶ G (n + 1)),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (G n)) ∧
      (∀ n : ℤ, (G n).IsFinitePresentation) ∧
      (∀ n : ℤ, (G n).IsQuasicoherent) ∧
      ∃ t : ∀ n : ℤ, (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hik))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE hik).op))).obj (G n) ≅
        (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (F n),
        ∀ n : ℤ, (Scheme.Modules.moduleBaseChange f
          (T := Over.mk (Spec.map (R.map (homOfLE hik))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE hik).op))).map (δ n) ≫
          (t (n + 1)).hom = (t n).hom ≫ φ n  := by
  classical
  let L := familyLimit R c f hij
  have descend (s : Finset ℤ) :
      ∃ (k : I) (_hjk : j ≤ k) (hik : i ≤ k)
        (G : ℤ → (pullback f (Spec.map (R.map (homOfLE hik)))).Modules)
        (δ : ∀ n : ℤ, G n ⟶ G (n + 1)),
        (∀ n : ℤ, n < a ∨ b < n → IsZero (G n)) ∧
        (∀ n : ℤ, (G n).IsFinitePresentation) ∧
        (∀ n : ℤ, (G n).IsQuasicoherent) ∧
        ∃ t : ∀ n : ℤ, (familyLimit R c f hik).obj (G n) ≅ L.obj (F n),
          ∀ n ∈ s, (familyLimit R c f hik).map (δ n) ≫
            (t (n + 1)).hom = (t n).hom ≫ φ n := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨j, le_refl j, hij, F, fun _ ↦ 0, hF_zero, hF_fp, hF_qc,
        fun _ ↦ Iso.refl _, by simp⟩
    | @insert n s hn ih =>
      obtain ⟨k, hjk, hik, G, δ, hGz, hGfp, hGqc, t, ht⟩ := ih
      let B := familyLimit R c f hik
      let ψlim := (t n).hom ≫ φ n ≫ (t (n + 1)).inv
      obtain ⟨k', hkk', ψ, e, _, hψ⟩ :=
        (finitePresentation_module_map_descent R c hc i f).2
          k hik (G n) (G (n + 1)) (hGfp n) (hGqc n)
          (hGfp (n + 1)) (hGqc (n + 1)) ψlim
      let T := familyTransition R f hik hkk'
      let B' := familyLimit R c f (hik.trans hkk')
      let H := fun m ↦ T.obj (G m)
      let δ' : ∀ m : ℤ, H m ⟶ H (m + 1) := fun m ↦
        if hm : m = n then by subst m; exact ψ else T.map (δ m)
      have hT : T.IsLeftAdjoint := by
        obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction
          (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE hik))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hik.trans hkk')))))
            (Over.homMk (Spec.map (R.map (homOfLE hkk')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
        exact adj.isLeftAdjoint
      have hHfp (m : ℤ) : (H m).IsFinitePresentation := by
        have := hGfp m
        exact Scheme.Modules.isFinitePresentation_tensorPullback _ _
      let t' := fun m ↦ (e.symm.app (G m)) ≪≫ t m
      refine ⟨k', hjk.trans hkk', hik.trans hkk', H, δ', ?_, hHfp, ?_, t', ?_⟩
      · intro m hm
        exact T.map_isZero (hGz m hm)
      · intro m
        have := hHfp m
        infer_instance
      · intro m hm
        dsimp only [t', Iso.trans_hom]
        by_cases hmn : m = n
        · subst m
          dsimp only [δ']
          rw [dite_eq_left rfl]
          have hp : B'.map ψ ≫ e.inv.app (G (n + 1)) =
              e.inv.app (G n) ≫ ψlim := by
            have h := congrArg (fun z ↦ e.inv.app (G n) ≫ z ≫
              e.inv.app (G (n + 1))) hψ
            simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
              Category.comp_id] at h
            exact h
          change B'.map ψ ≫ e.inv.app (G (n + 1)) ≫ (t (n + 1)).hom =
            (e.inv.app (G n) ≫ (t n).hom) ≫ φ n
          have h := congrArg (fun z ↦ z ≫ (t (n + 1)).hom) hp
          simpa [ψlim, Category.assoc] using h
        · dsimp only [δ']
          rw [dite_eq_right hmn]
          have hm' : m ∈ s := (Finset.mem_insert.mp hm).resolve_left hmn
          have he := e.inv.naturality (δ m)
          change B'.map (T.map (δ m)) ≫ e.inv.app (G (m + 1)) =
            e.inv.app (G m) ≫ B.map (δ m) at he
          change B'.map (T.map (δ m)) ≫ e.inv.app (G (m + 1)) ≫
            (t (m + 1)).hom = (e.inv.app (G m) ≫ (t m).hom) ≫ φ m
          have h := congrArg (fun z ↦ z ≫ (t (m + 1)).hom) he
          have hh : B.map (δ m) ≫ (t (m + 1)).hom = (t m).hom ≫ φ m := ht m hm'
          simpa only [Category.assoc, hh] using h
  obtain ⟨k, hjk, hik, G, δ, hGz, hGfp, hGqc, t, ht⟩ :=
    descend (Finset.Icc a (b - 1))
  refine ⟨k, hjk, hik, G, δ, hGz, hGfp, hGqc, t, ?_⟩
  intro n
  by_cases hn : n ∈ Finset.Icc a (b - 1)
  · exact ht n hn
  · have hnb : n < a ∨ b < n + 1 := by
      simp only [Finset.mem_Icc] at hn
      omega
    rcases hnb with hna | hbn
    · exact (familyLimit_isZero R c f hik _ (hGz n (Or.inl hna))).eq_of_src _ _
    · exact (familyLimit_isZero R c f hij _ (hF_zero (n + 1) (Or.inr hbn))).eq_of_tgt _ _
end AlgebraicGeometry
