/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.Homology.BoundedGradedMapColimitDescent

/-! # Descent of the maps of a bounded graded family

Source: Stacks Project, Tag 0BC7, proof of (1), using Tag 05N7, clause (2).
(blueprint: lem-pc-bounded-graded-family-map-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Descend the maps of a bounded graded family, without imposing composite relations.

Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), using Algebra,
Tag 05N7, clause (2).
(blueprint: lem-pc-bounded-graded-family-map-colimit-descent).

Proof: Regard the fixed terms M n as a cochain complex C with zero differentials,
and the shifted terms M (n+1) as a second such complex B. Conjugate the adjacent
maps of Q by e to obtain graded components from the colimit extension of C to
that of B. Apply bounded graded component-map descent to C and B. The source
bounds are exactly hzero and both term families are finitely presented by hfp.
The components of its canonical complex comparison are the canonical module
scalar-extension comparisons. Their inverses followed by e give a single family
e' for all degrees. Define d m n by the descended component when m+1=n and zero
otherwise. Cancel the comparison isomorphisms in the descended equation to prove
the adjacent compatibility squares; in nonadjacent degrees both maps are zero.
No square-zero condition is imposed on these adjacent maps. Empty bounds and
preorders are included by the component-map theorem. -/
theorem exists_bounded_graded_maps_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (Q : ℤ → ModuleCat.{u} (colimit F : CommRingCat.{u}))
    (δ : ∀ m n : ℤ, Q m ⟶ Q n)
    (hδ : ∀ m n : ℤ, ¬ (ComplexShape.up ℤ).Rel m n → δ m n = 0)
    (i : I) (M : ℤ → ModuleCat.{u} (F.obj i)) (a b : ℤ)
    (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (M n))
    (hfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i) (M n))
    (e : ∀ n : ℤ, (extendScalars (colimit.ι F i).hom).obj (M n) ≅ Q n) :
    ∃ (j : I) (hij : i ≤ j),
      let G := extendScalars (F.map (homOfLE hij)).hom
      let E := extendScalars (colimit.ι F j).hom
      ∃ (d : ∀ m n : ℤ, G.obj (M m) ⟶ G.obj (M n))
        (e' : ∀ n : ℤ, E.obj (G.obj (M n)) ≅ Q n),
        (∀ m n : ℤ, ¬ (ComplexShape.up ℤ).Rel m n → d m n = 0) ∧
        (∀ m n : ℤ, (e' m).hom ≫ δ m n = E.map (d m n) ≫ (e' n).hom) := by
  classical
  let C : CochainComplex (ModuleCat.{u} (F.obj i)) ℤ :=
    { X := M, d := fun _ _ => 0 }
  let B : CochainComplex (ModuleCat.{u} (F.obj i)) ℤ :=
    { X := fun n => M (n + 1), d := fun _ _ => 0 }
  let f (n : ℤ) := (e n).hom ≫ δ n (n + 1) ≫ (e (n + 1)).inv
  obtain ⟨j, v, hv⟩ := CochainComplex.exists_bounded_graded_map_of_directed_colimit
    F i C B a b hzero hfp (fun n => hfp (n + 1)) f
  let G := extendScalars (F.map (homOfLE j.property)).hom
  let E := extendScalars (colimit.ι F j.val).hom
  have hr : (colimit.ι F j.val).hom.comp (F.map (homOfLE j.property)).hom =
      (colimit.ι F i).hom := by
    rw [← CommRingCat.hom_comp, colimit.w]
  let c : extendScalars (colimit.ι F i).hom ≅ G ⋙ E :=
    eqToIso (congrArg extendScalars hr.symm) ≪≫
      extendScalarsComp (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom
  have hv' (n : ℤ) : (c.app (M n)).hom ≫ E.map (v n) ≫
      (c.app (M (n + 1))).inv = f n := by
    simpa only [C, B, c, G, E, Iso.trans_hom, Iso.trans_inv,
      HomologicalComplex.comp_f, eqToIso.hom, eqToIso.inv,
      Iso.app_hom, Iso.app_inv, HomologicalComplex.eqToHom_f,
      NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f,
      eqToHom_app, NatTrans.comp_app] using hv n
  let e' (n : ℤ) := (c.app (M n)).symm ≪≫ e n
  let d (m n : ℤ) : G.obj (M m) ⟶ G.obj (M n) :=
    if h : m + 1 = n then v m ≫ eqToHom (congrArg (fun n => G.obj (M n)) h)
    else 0
  refine ⟨j.val, j.property, d, e', ?_, ?_⟩
  · intro m n h
    exact dite_eq_right h
  · intro m n
    by_cases h : m + 1 = n
    · subst n
      have hh := hv' m
      dsimp [f] at hh
      have hh' := congrArg (fun z => (c.app (M m)).inv ≫ z ≫ (e (m + 1)).hom) hh
      simpa [d, e', Category.assoc] using hh'.symm
    · dsimp [d]
      rw [dite_eq_right h, hδ m n h, E.map_zero]
      simp

end ModuleCat
