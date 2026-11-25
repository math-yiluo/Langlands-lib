/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.Homology.BoundedGradedFamilyMapColimitDescent
import WeilConjectures.Algebra.FiniteFamilyModuleMapEqualityColimit
import Mathlib.Data.Int.Interval

/-! # Descent of differentials on fixed bounded graded module models

Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), descent of maps and relations.
(blueprint: lem-pc-affine-differential-colimit-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- On fixed bounded finitely presented term models, the differentials and their zero-composite
relations descend after extending those models to a later stage.
Source: Stacks Project, More on Algebra, Tag 0BC7, proof of (1), via Algebra, Tag 05N7.
(blueprint: lem-pc-affine-differential-colimit-descent).

Proof: Transport each differential of P across the given term isomorphisms. Only adjacent
pairs with both degrees in [a,b] can have a nonzero differential. Descend this finite list
by the map clause of finite-presentation colimit descent, and choose one common later stage.
Use the canonical iterated extension-of-scalars isomorphisms to keep all the descended maps
compatible with one common family of term isomorphisms. Each consecutive composite becomes
zero after extension to the colimit, because it is conjugate to a composite in P. Apply the
equality clause of finite-presentation colimit descent to these finitely many composites
and the zero maps, and pass to a common later stage. Put zero in nonadjacent degrees and
where either term is outside the interval; scalar extension preserves zero objects, so
compatibility there is automatic. Composition of the retained adjacent maps is zero by
the imposed relations; all other composites contain a zero map. Return the maps and the
compatible term isomorphisms. No complex is constructed here. For a preorder, pass to its
antisymmetrization as an indexing category to use the partial-order finite-presentation
lemma and lift the later index back (equivalence preserves and reflects the order relation).
For an empty interval all models are zero, so all returned maps are zero. -/
theorem exists_differentials_on_graded_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (P : CochainComplex (ModuleCat.{u} (colimit F : CommRingCat.{u})) ℤ)
    (i : I) (M : ℤ → ModuleCat.{u} (F.obj i)) (a b : ℤ)
    (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (M n))
    (hfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i) (M n))
    (e : ∀ n : ℤ, (ModuleCat.extendScalars (colimit.ι F i).hom).obj (M n) ≅ P.X n) :
    ∃ (j : I) (hij : i ≤ j),
      let G := ModuleCat.extendScalars (F.map (homOfLE hij)).hom
      let E := ModuleCat.extendScalars (colimit.ι F j).hom
      ∃ (d : ∀ m n : ℤ, G.obj (M m) ⟶ G.obj (M n))
        (e' : ∀ n : ℤ, E.obj (G.obj (M n)) ≅ P.X n),
        (∀ m n : ℤ, ¬ (ComplexShape.up ℤ).Rel m n → d m n = 0) ∧
        (∀ m n k : ℤ, d m n ≫ d n k = 0) ∧
        (∀ m n : ℤ, (e' m).hom ≫ P.d m n = E.map (d m n) ≫ (e' n).hom) := by
  obtain ⟨j, hij, d, e', hshape, hcomm⟩ :=
    ModuleCat.exists_bounded_graded_maps_of_directed_colimit F P.X P.d
      (fun m n h => P.shape m n h) i M a b hzero hfp e
  let G := ModuleCat.extendScalars (F.map (homOfLE hij)).hom
  let E := ModuleCat.extendScalars (colimit.ι F j).hom
  have hGfp (n : ℤ) : Module.FinitePresentation (F.obj j) (G.obj (M n)) := by
    let := hfp n
    let : Algebra (F.obj i) (F.obj j) := (F.map (homOfLE hij)).hom.toAlgebra
    change Module.FinitePresentation (F.obj j) (TensorProduct (F.obj i) (F.obj j) (M n))
    infer_instance
  have hcomp (m n k : ℤ) : E.map (d m n ≫ d n k) = 0 := by
    apply (cancel_mono (e' k).hom).1
    calc
      E.map (d m n ≫ d n k) ≫ (e' k).hom =
          (e' m).hom ≫ (P.d m n ≫ P.d n k) := by
        rw [E.map_comp, Category.assoc, ← hcomm n k,
          ← Category.assoc, ← hcomm m n, Category.assoc]
      _ = 0 ≫ (e' k).hom := by simp
  let T := {n : ℤ // n ∈ Finset.Icc a b}
  have hT : Finite T := inferInstance
  obtain ⟨k, hjk, hk⟩ := ModuleCat.exists_stage_finite_family_map_eq F j (T := T)
    (fun t : T => G.obj (M t.val)) (fun t : T => G.obj (M (t.val + 2)))
    (fun t : T => hGfp t.val) (fun t : T => hGfp (t.val + 2))
    (fun t : T => d t.val (t.val + 1) ≫ d (t.val + 1) (t.val + 2))
    (fun _ => 0) (fun t : T => by
      change E.map (d t.val (t.val + 1) ≫ d (t.val + 1) (t.val + 2)) = E.map 0
      rw [hcomp, E.map_zero])
  let H := ModuleCat.extendScalars (F.map (homOfLE hjk)).hom
  have hHcomp (m n l : ℤ) : H.map (d m n ≫ d n l) = 0 := by
    by_cases hmn : (ComplexShape.up ℤ).Rel m n
    · by_cases hnl : (ComplexShape.up ℤ).Rel n l
      · have hn : m + 1 = n := hmn
        have hl : n + 1 = l := hnl
        by_cases hm : m ∈ Finset.Icc a b
        · subst n
          have : l = m + 2 := by omega
          subst l
          have hh := hk ⟨m, hm⟩
          change H.map (d m (m + 1) ≫ d (m + 1) (m + 2)) = H.map 0 at hh
          rw [H.map_zero] at hh
          have hadd : m + 1 + 1 = m + 2 := by omega
          rw [hadd]
          exact hh
        · have hm' : m < a ∨ b < m := by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hm
            exact hm
          rw [(G.map_isZero (hzero m hm')).eq_zero_of_src (d m n)]
          simp only [zero_comp, H.map_zero]
      · rw [hshape n l hnl]
        simp only [comp_zero, H.map_zero]
    · rw [hshape m n hmn]
      simp only [zero_comp, H.map_zero]
  let hik := hij.trans hjk
  let K := ModuleCat.extendScalars (F.map (homOfLE hik)).hom
  let L := ModuleCat.extendScalars (colimit.ι F k).hom
  have hring : (F.map (homOfLE hjk)).hom.comp (F.map (homOfLE hij)).hom =
      (F.map (homOfLE hik)).hom := by
    rw [← CommRingCat.hom_comp, ← F.map_comp]
    rfl
  let c : K ≅ G ⋙ H :=
    eqToIso (congrArg ModuleCat.extendScalars hring.symm) ≪≫
      ModuleCat.extendScalarsComp (F.map (homOfLE hij)).hom (F.map (homOfLE hjk)).hom
  have hcolim : (colimit.ι F k).hom.comp (F.map (homOfLE hjk)).hom =
      (colimit.ι F j).hom := by
    rw [← CommRingCat.hom_comp, colimit.w]
  let v : E ≅ H ⋙ L :=
    eqToIso (congrArg ModuleCat.extendScalars hcolim.symm) ≪≫
      ModuleCat.extendScalarsComp (F.map (homOfLE hjk)).hom (colimit.ι F k).hom
  let D (m n : ℤ) : K.obj (M m) ⟶ K.obj (M n) :=
    (c.app (M m)).hom ≫ H.map (d m n) ≫ (c.app (M n)).inv
  let e'' (n : ℤ) : L.obj (K.obj (M n)) ≅ P.X n :=
    L.mapIso (c.app (M n)) ≪≫ (v.app (G.obj (M n))).symm ≪≫ e' n
  refine ⟨k, hik, D, e'', ?_, ?_, ?_⟩
  · intro m n h
    change (c.app (M m)).hom ≫ H.map (d m n) ≫ (c.app (M n)).inv = 0
    rw [hshape m n h, H.map_zero]
    simp
  · intro m n l
    change ((c.app (M m)).hom ≫ H.map (d m n) ≫ (c.app (M n)).inv) ≫
      ((c.app (M n)).hom ≫ H.map (d n l) ≫ (c.app (M l)).inv) = 0
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (H.map (d m n)), ← H.map_comp, hHcomp m n l]
    simp
  · intro m n
    change (L.map (c.app (M m)).hom ≫ (v.app (G.obj (M m))).inv ≫ (e' m).hom) ≫
      P.d m n = L.map ((c.app (M m)).hom ≫ H.map (d m n) ≫
        (c.app (M n)).inv) ≫
        (L.map (c.app (M n)).hom ≫ (v.app (G.obj (M n))).inv ≫ (e' n).hom)
    simp only [Category.assoc, hcomm, L.map_comp]
    rw [← L.map_comp_assoc (c.app (M n)).inv (c.app (M n)).hom,
      (c.app (M n)).inv_hom_id, L.map_id, Category.id_comp]
    have hv := v.inv.naturality (d m n)
    change L.map (H.map (d m n)) ≫ (v.app (G.obj (M n))).inv =
      (v.app (G.obj (M m))).inv ≫ E.map (d m n) at hv
    rw [← Category.assoc (v.app (G.obj (M m))).inv, ← hv]
    simp only [Category.assoc]

end CochainComplex
