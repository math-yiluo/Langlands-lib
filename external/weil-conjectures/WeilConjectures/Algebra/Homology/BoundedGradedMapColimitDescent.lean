/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder

import WeilConjectures.Algebra.FinitePresentationMapCanonical
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Order

/-! # Descent of bounded families of graded maps

Source: Stacks Project, Tag 09RE, affine case (1), and Tag 05N7, map clause.
(blueprint: lem-pc-bounded-graded-map-colimit-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem transport
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (p : R →+* S) (q : S →+* T) (r : T →+* A)
    (M N : ModuleCat.{u} R)
    (v : (extendScalars p).obj M ⟶ (extendScalars p).obj N) :
    let w := (extendScalarsComp p q).hom.app M ≫ (extendScalars q).map v ≫
      (extendScalarsComp p q).inv.app N
    (extendScalarsComp (q.comp p) r).hom.app M ≫ (extendScalars r).map w ≫
      (extendScalarsComp (q.comp p) r).inv.app N =
    (extendScalarsComp p (r.comp q)).hom.app M ≫
      (extendScalars (r.comp q)).map v ≫ (extendScalarsComp p (r.comp q)).inv.app N := by
  dsimp only
  simp only [Functor.map_comp, Category.assoc]
  have hass (X : ModuleCat R) :
      (extendScalarsComp (q.comp p) r).hom.app X ≫
        (extendScalars r).map ((extendScalarsComp p q).hom.app X) =
      (extendScalarsComp p (r.comp q)).hom.app X ≫
        (extendScalarsComp q r).hom.app ((extendScalars p).obj X) := by
    have h := congrArg (fun α ↦ α.app X) (extendScalars_assoc p q r)
    dsimp at h
    simpa only [Category.comp_id] using h
  have hinv (X : ModuleCat R) :
      (extendScalars r).map ((extendScalarsComp p q).inv.app X) ≫
        (extendScalarsComp (q.comp p) r).inv.app X =
      (extendScalarsComp q r).inv.app ((extendScalars p).obj X) ≫
        (extendScalarsComp p (r.comp q)).inv.app X := by
    have h : (extendScalarsComp (q.comp p) r).app X ≪≫
        (extendScalars r).mapIso ((extendScalarsComp p q).app X) =
        (extendScalarsComp p (r.comp q)).app X ≪≫
        (extendScalarsComp q r).app ((extendScalars p).obj X) := by
      apply Iso.ext
      exact hass X
    exact congrArg Iso.inv h
  rw [← Category.assoc, hass M, Category.assoc, hinv N]
  change _ ≫ (extendScalarsComp q r).hom.app _ ≫
    (extendScalars q ⋙ extendScalars r).map v ≫ _ = _
  rw [← (extendScalarsComp q r).hom.naturality_assoc v]
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem transportComparisons
    {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    (p : R →+* S) (p' : R →+* T) (q : S →+* T)
    (ri : S →+* A) (rj : T →+* A) (r0 : R →+* A)
    (hp : p' = q.comp p) (hi : ri = rj.comp q)
    (h0i : r0 = ri.comp p) (h0j : r0 = rj.comp p')
    (M N : ModuleCat.{u} R)
    (v : (extendScalars p).obj M ⟶ (extendScalars p).obj N) :
    let ei (X : ModuleCat R) := eqToIso (congrArg (fun r ↦ (extendScalars r).obj X) h0i) ≪≫
      (extendScalarsComp p ri).app X
    let ej (X : ModuleCat R) := eqToIso (congrArg (fun r ↦ (extendScalars r).obj X) h0j) ≪≫
      (extendScalarsComp p' rj).app X
    ∃ w : (extendScalars p').obj M ⟶ (extendScalars p').obj N,
      (ej M).hom ≫ (extendScalars rj).map w ≫ (ej N).inv =
      (ei M).hom ≫ (extendScalars ri).map v ≫ (ei N).inv := by
  subst p'
  subst ri
  subst r0
  refine ⟨(extendScalarsComp p q).hom.app M ≫ (extendScalars q).map v ≫
    (extendScalarsComp p q).inv.app N, ?_⟩
  simpa [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Iso.trans_hom, Iso.trans_inv,
    Category.id_comp, Category.comp_id, Iso.app_hom, Iso.app_inv] using transport p q rj M N v

end ModuleCat

namespace CochainComplex

/-- Descend the components of a graded map, without imposing chain-map equations.

Source: Stacks Project, Tag 09RE, affine case (1), via Tag 05N7 (2).
Proof: Only degrees in [a,b] need nonzero components. Each source and target term is
finitely presented, so the map clause of finite-presentation descent lifts each of these
finitely many components to a stage above i₀. Directedness gives a common upper stage;
extend each lifted map to that stage and conjugate by scalar-extension associativity.
The canonical comparison sends 1 tensor x to 1 tensor (1 tensor x), so its conjugation
agrees with the comparison in Tag 05N7. Outside the interval the source is zero, and
scalar extension preserves zero objects; put zero there. This also proves the required
comparison in those degrees. For a preorder, the presentation-matrix proof of Tag 05N7
uses only finitely many coefficients, relations and directed upper bounds, so works
without antisymmetry, using the filtered-ring elementwise criterion. Equivalently,
pass to the antisymmetrization, transport along its category equivalence, and lift the
resulting index to an upper bound with i₀. If b < a all source terms are zero, and the
zero family at i₀ suffices.
(blueprint: lem-pc-bounded-graded-map-colimit-descent) -/
theorem exists_bounded_graded_map_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (P Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (a b : ℤ) (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hP : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (P.X n))
    (hQ : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (Q.X n))
    (f : ∀ n : ℤ,
      (ModuleCat.extendScalars (colimit.ι F i₀).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (colimit.ι F i₀).hom).obj (Q.X n)) :
    let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
      eqToIso (congrArg (fun r ↦
        ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (NatIso.mapHomologicalComplex
        (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
          (colimit.ι F t.val).hom) (.up ℤ)).app C
    ∃ (i : Set.Ici i₀)
      (v : ∀ n : ℤ,
        (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (P.X n) ⟶
          (ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).obj (Q.X n)),
      ∀ n : ℤ, (e i P).hom.f n ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
          (e i Q).inv.f n = f n := by
  classical
  dsimp only
  let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
    eqToIso (congrArg (fun r ↦
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
    (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
        (colimit.ι F t.val).hom) (.up ℤ)).app C
  have hdesc (n : ℤ) :=
    ModuleCat.finitePresentation_map_directedColimit F i₀
      (P.X n) (Q.X n) (hP n) (hQ n) (f n)
  dsimp only at hdesc
  choose j hj using hdesc
  let : Nonempty I := ⟨i₀⟩
  obtain ⟨i, hi⟩ :=
    (insert i₀ ((Finset.Icc a b).image (fun n ↦ (j n).val))).exists_le
  let t : Set.Ici i₀ := ⟨i, hi i₀ (Finset.mem_insert_self _ _)⟩
  have hlift (n : ℤ) :
      ∃ v : (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (P.X n) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (Q.X n),
        (e t P).hom.f n ≫ (ModuleCat.extendScalars (colimit.ι F t.val).hom).map v ≫
          (e t Q).inv.f n = f n := by
    by_cases hn : n ∈ Finset.Icc a b
    · obtain ⟨v, hv⟩ := hj n
      have hji : (j n).val ≤ t.val := hi (j n).val
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
      have hp : (F.map (homOfLE t.property)).hom =
          (F.map (homOfLE hji)).hom.comp (F.map (homOfLE (j n).property)).hom := by
        rw [← CommRingCat.hom_comp, ← F.map_comp]
        rfl
      have hi' : (colimit.ι F (j n).val).hom =
          (colimit.ι F t.val).hom.comp (F.map (homOfLE hji)).hom := by
        exact (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hji))).symm
      obtain ⟨w, hw⟩ := ModuleCat.transportComparisons
        (F.map (homOfLE (j n).property)).hom (F.map (homOfLE t.property)).hom
        (F.map (homOfLE hji)).hom (colimit.ι F (j n).val).hom
        (colimit.ι F t.val).hom (colimit.ι F i₀).hom hp hi'
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE (j n).property))).symm
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property))).symm
        (P.X n) (Q.X n) v
      refine ⟨w, ?_⟩
      have hv' := hw.trans hv
      simpa only [e, Iso.trans_hom, Iso.trans_inv, HomologicalComplex.comp_f,
        eqToIso.hom, eqToIso.inv, HomologicalComplex.eqToHom_f,
        Iso.app_hom, Iso.app_inv,
        NatIso.mapHomologicalComplex_hom_app_f, NatIso.mapHomologicalComplex_inv_app_f]
        using hv'
    · refine ⟨0, ?_⟩
      have hz : IsZero (P.X n) := hzero n (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        exact hn)
      exact (Functor.map_isZero (ModuleCat.extendScalars (colimit.ι F i₀).hom) hz).eq_of_src
        _ _
  choose v hv using hlift
  exact ⟨t, v, hv⟩

end CochainComplex
