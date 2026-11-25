/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.BoundedGradedModuleMapDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackFinitePresentation
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.EquivFin
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.AlgebraicGeometry.FiniteRelationDescent

/-!
# Descent of bounded finitely presented complexes

Source: Stacks Project, Limits of Schemes, Lemma 32.10.2 (Tag 01ZR), in the
Noetherian approximation setting of Lemma 32.10.4 (Tag 05LY)
(blueprint: lem-pc-fp-complex-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A bounded complex of finitely presented quasi-coherent modules on the limit base change
of a finitely presented scheme descends to some later stage.
Source: Stacks Project, Limits of Schemes, Tag 01ZR; Noetherian approximation setting of
Tag 05LY (blueprint: lem-pc-fp-complex-descent).

The functor `R` presents the inverse system of affine schemes contravariantly. Affine
schemes are quasi-compact and quasi-separated, and the transition maps between spectra
are affine. `c` is its limit cone; `IsAffine c.pt` expresses `S = Spec R` without choosing
a coordinate ring. Finite presentation of `f` includes quasi-separatedness as specified
by `def-pc-morphism-conventions`. A cochain complex includes the equations `d ≫ d = 0`.
The isomorphism of complexes is expressed by termwise isomorphisms commuting with all
differentials. Module base change is `moduleBaseChange`, hence tensor pullback, not the
restriction-of-scalars functor `Scheme.Modules.pullback`.

Proof:
1. Boundedness leaves finitely many terms, differentials, and equations that consecutive
   differentials compose to zero; these form finite module-and-map data.
2. Apply part (1) of `lem-pc-fp-module-map-descent` to these terms, choosing a common later
   stage by directedness. Apply part (2) to the differentials between these fixed models,
   transported using their pullback isomorphisms. Choose another common stage, keeping
   one model for each term shared by consecutive differentials.
3. Apply `lem-pc-fp-relation-descent` to the finitely many equations `d ≫ d = 0`. They hold
   after passing to one further stage, since their pullbacks are the zero composites of G.
4. Extend by zero outside the finite interval. The terms and maps form the bounded complex
   H; the termwise pullback isomorphisms commute with the differentials by step 2 and
   therefore give an isomorphism of complexes. -/
theorem exists_finitelyPresented_complex_of_limit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (pullback f (c.π.app (op i))).Modules ℤ)
    (hG_bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hG_fp : ∀ n : ℤ, (G.X n).IsFinitePresentation)
    (hG_qc : ∀ n : ℤ, (G.X n).IsQuasicoherent) :
    ∃ (j : I) (hij : i ≤ j)
      (H : CochainComplex (pullback f (Spec.map (R.map (homOfLE hij)))).Modules ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (H.X n)) ∧
      (∀ n : ℤ, (H.X n).IsFinitePresentation) ∧
      (∀ n : ℤ, (H.X n).IsQuasicoherent) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (H.X n) ≅ G.X n,
        ∀ n m : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (H.d n m) ≫
              (e m).hom = (e n).hom ≫ G.d n m := by
  classical
  obtain ⟨a, b, hG_zero⟩ := hG_bounded
  obtain ⟨j, hij, F, δ, hF_zero, hF_fp, hF_qc, e, he⟩ :=
    bounded_graded_module_map_descent R c hc i f G.X a b hG_zero hG_fp hG_qc
      (fun n ↦ G.d n (n + 1))
  let gB : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)
  let B := Scheme.Modules.moduleBaseChange f gB
  have adjB := (Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f gB)).some
  let : B.IsLeftAdjoint := adjB.isLeftAdjoint
  have hsq (n : ℤ) : B.map (δ n ≫ δ (n + 1)) = B.map 0 := by
    apply (cancel_mono (e (n + 1 + 1)).hom).1
    simp only [Functor.map_comp, Functor.map_zero, zero_comp]
    rw [Category.assoc, he (n + 1), ← Category.assoc, he n, Category.assoc,
      G.d_comp_d, comp_zero]
  -- Enumerate only the potentially nonzero square relations.
  let N := {n : ℤ // n ∈ Finset.Icc a b}
  let K := ULift.{u} {n : ℤ // n ∈ Finset.Icc a (b + 2)}
  let q : Fin (Fintype.card N) ≃ N := (Fintype.equivFin N).symm
  let src (k : Fin (Fintype.card N)) : K :=
    ⟨⟨(q k).val, by
      have hn := (q k).property
      simp only [Finset.mem_Icc] at hn ⊢
      omega⟩⟩
  let tgt (k : Fin (Fintype.card N)) : K :=
    ⟨⟨(q k).val + 1 + 1, by
      have hn := (q k).property
      simp only [Finset.mem_Icc] at hn ⊢
      omega⟩⟩
  let models (k : K) := F k.down.val
  let lhs (k : Fin (Fintype.card N)) : models (src k) ⟶ models (tgt k) :=
    δ (q k).val ≫ δ ((q k).val + 1)
  obtain ⟨j', hjj', hrelations⟩ := finiteRelation_module_map_descent R c hc i f j hij K
    models (fun k ↦ hF_fp k.down.val) (fun k ↦ hF_qc k.down.val)
    (Fintype.card N) src tgt lhs (fun _ ↦ 0) (fun k ↦ hsq (q k).val)
  let g : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjj')))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  let h : Over.mk (c.π.app (op i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))) :=
    Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)
  let P := Scheme.Modules.moduleBaseChange f g
  let B' := Scheme.Modules.moduleBaseChange f h
  let : P.IsLeftAdjoint :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction (baseChangeMap f g)).some.isLeftAdjoint
  have hsquare (n : ℤ) : P.map (δ n) ≫ P.map (δ (n + 1)) = 0 := by
    rw [← P.map_comp]
    by_cases hn : n ∈ Finset.Icc a b
    · have hr (z : N) : P.map (δ z.val ≫ δ (z.val + 1)) = P.map 0 := by
        obtain ⟨k, rfl⟩ := q.surjective z
        exact hrelations k
      simpa only [Functor.map_zero] using hr ⟨n, hn⟩
    · have hz : IsZero (F n) := hF_zero n (by
        simp only [Finset.mem_Icc] at hn
        omega)
      rw [hz.eq_of_src (δ n ≫ δ (n + 1)) 0, Functor.map_zero]
  let H := CochainComplex.of (fun n ↦ P.obj (F n)) (fun n ↦ P.map (δ n)) hsquare
  have hcomp : baseChangeMap f h ≫ baseChangeMap f g =
      baseChangeMap f gB := by
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa [g, h, gB] using c.w (homOfLE hjj').op
  obtain ⟨t⟩ := Scheme.Modules.nonempty_tensorPullbackComp
    (baseChangeMap f h) (baseChangeMap f g)
  let β : B ≅ P ⋙ B' :=
    (eqToIso (congrArg Scheme.Modules.tensorPullback hcomp)).symm ≪≫ t
  let e' (n : ℤ) : B'.obj (H.X n) ≅ G.X n := (β.symm.app (F n)) ≪≫ e n
  have he' (n : ℤ) : B'.map (P.map (δ n)) ≫ (e' (n + 1)).hom =
      (e' n).hom ≫ G.d n (n + 1) := by
    change (P ⋙ B').map (δ n) ≫ ((β.symm.app (F (n + 1))).hom ≫ (e (n + 1)).hom) =
      ((β.symm.app (F n)).hom ≫ (e n).hom) ≫ G.d n (n + 1)
    change (P ⋙ B').map (δ n) ≫ (β.inv.app (F (n + 1)) ≫ (e (n + 1)).hom) =
      (β.inv.app (F n) ≫ (e n).hom) ≫ G.d n (n + 1)
    rw [← Category.assoc, β.inv.naturality, Category.assoc, he n, Category.assoc]
  refine ⟨j', hij.trans hjj', H, ⟨a, b, ?_⟩, ?_, ?_, e', ?_⟩
  · intro n hn
    exact P.map_isZero (hF_zero n hn)
  · intro n
    let := hF_fp n
    exact Scheme.Modules.isFinitePresentation_tensorPullback (baseChangeMap f g) (F n)
  · intro n
    let := hF_fp n
    change (P.obj (F n)).IsQuasicoherent
    let : (P.obj (F n)).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_tensorPullback (baseChangeMap f g) (F n)
    infer_instance
  · intro n m
    by_cases hnm : n + 1 = m
    · subst m
      simpa only [H, CochainComplex.of_d] using he' n
    · have hG : G.d n m = 0 := G.shape n m hnm
      change B'.map (CochainComplex.of.d _ _ n m) ≫ _ = _
      rw [CochainComplex.of_d_ne _ _ hnm, hG]
      let : B'.IsLeftAdjoint :=
        (Scheme.Modules.nonempty_tensorPullbackAdjunction
          (baseChangeMap f h)).some.isLeftAdjoint
      simp


end AlgebraicGeometry
