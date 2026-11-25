/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.FinitePresentation

import WeilConjectures.Algebra.Homology.BoundedGradedMapColimitDescent

/-! # AffinePerfectGradedHomDescent

Source: Stacks Project, Tags 09RE and 05N7.
(blueprint: lem-pc-affine-perfect-graded-hom-descent)
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

set_option linter.unusedVariables false in
/-- Descend a degree-minus-one graded family without imposing chain-map or homotopy equations.

Source: Stacks Project, Tag 09RE, affine case (1), finite number of finitely
presented source terms; Tag 05N7 (2).
Proof: In the finite interval supporting E₀, descend each component s(m,m-1)
using finite-presentation map descent. The source and target terms are finitely
presented by hypothesis. Directedness gives one common stage above i.
Transport all components to that stage by scalar-extension associativity, and
put zero outside the interval. Components of a different degree are not required.
The canonical comparison isomorphisms in map descent are uniquely determined
by their value on tensors 1 ⊗ x, and hence are precisely extendScalarsComp,
after the equality hc identifies the ring homomorphisms. Thus the transported
components have exactly the stated equality with s. On zero source terms this
is automatic, since scalar extension preserves zero objects. No relation with
any differential or prescribed chain map is asserted. For a preorder take the
quotient by mutual comparability, choose representatives, and use the equivalent
partial-order index category in finite-presentation descent. Ring maps between
equivalent indices are inverse isomorphisms. Transport back and take an upper
bound with i. An empty support interval gives the zero family at any stage above i.
(blueprint: lem-pc-affine-perfect-graded-hom-descent) -/
theorem affine_perfect_gradedHom_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n))
    (hEfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (E₀.X n))
    (hKfp : ∀ n : ℤ, Module.FinitePresentation (F.obj i₀) (K₀.X n))
    (i : Set.Ici i₀)
    (s : ∀ m n : ℤ, (ComplexShape.up ℤ).Rel n m →
      ((((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
      (.up ℤ)).obj E₀).X m ⟶ (((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
      (.up ℤ)).obj K₀).X n)) :
    ∃ (j : Set.Ici i₀) (hij : i ≤ j)
      (t : ∀ m n : ℤ, (ComplexShape.up ℤ).Rel n m →
        ((((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀).X m ⟶
          (((ModuleCat.extendScalars (F.map (homOfLE j.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀).X n)),
      let hc := congrArg CommRingCat.Hom.hom
        (colimit.w F (homOfLE j.property)).symm
      let L := eqToHom (congrArg (fun r ↦
          ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀) hc) ≫
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom) (.up ℤ)).hom.app E₀
      let R := (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp
          (F.map (homOfLE j.property)).hom (colimit.ι F j.val).hom) (.up ℤ)).inv.app K₀ ≫
        eqToHom (congrArg (fun r ↦
          ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀) hc.symm)
      ∀ m n : ℤ, ∀ hmn : (ComplexShape.up ℤ).Rel n m,
        L.f m ≫ (ModuleCat.extendScalars (colimit.ι F j.val).hom).map (t m n hmn) ≫
          R.f n = s m n hmn := by
  classical
  obtain ⟨a, b, hzero⟩ := hbounded
  let Q : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ :=
    { X := fun m ↦ K₀.X (m - 1)
      d := fun _ _ ↦ 0
      shape := by intros; rfl
      d_comp_d' := by intros; simp }
  have hrel (m : ℤ) : (ComplexShape.up ℤ).Rel (m - 1) m := by
    change m - 1 + 1 = m
    omega
  obtain ⟨j, v, hv⟩ := exists_bounded_graded_map_of_directed_colimit
    F i₀ E₀ Q a b hzero hEfp (fun m ↦ hKfp (m - 1))
      (fun m ↦ s m (m - 1) (hrel m))
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.val j.val
  let t : Set.Ici i₀ := ⟨k, i.property.trans hik⟩
  let e (t : Set.Ici i₀) (X : ModuleCat.{u} (F.obj i₀)) :=
    eqToIso (congrArg (fun r ↦ (ModuleCat.extendScalars r).obj X)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
      (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
        (colimit.ι F t.val).hom).app X
  have hp : (F.map (homOfLE t.property)).hom =
      (F.map (homOfLE hjk)).hom.comp (F.map (homOfLE j.property)).hom := by
    rw [← CommRingCat.hom_comp, ← F.map_comp]
    rfl
  have hi' : (colimit.ι F j.val).hom =
      (colimit.ι F t.val).hom.comp (F.map (homOfLE hjk)).hom := by
    exact (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hjk))).symm
  have hlift (m : ℤ) :
      ∃ w : (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (E₀.X m) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (K₀.X (m - 1)),
        (e t (E₀.X m)).hom ≫ (ModuleCat.extendScalars (colimit.ι F t.val).hom).map w ≫
          (e t (K₀.X (m - 1))).inv = s m (m - 1) (hrel m) := by
    obtain ⟨w, hw⟩ := ModuleCat.transportComparisons
      (F.map (homOfLE j.property)).hom (F.map (homOfLE t.property)).hom
      (F.map (homOfLE hjk)).hom (colimit.ι F j.val).hom
      (colimit.ι F t.val).hom (colimit.ι F i₀).hom hp hi'
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.property))).symm
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property))).symm
      (E₀.X m) (K₀.X (m - 1)) (v m)
    refine ⟨w, hw.trans ?_⟩
    simpa only [Iso.trans_hom, Iso.trans_inv, HomologicalComplex.comp_f,
      eqToIso.hom, eqToIso.inv, HomologicalComplex.eqToHom_f,
      Iso.app_hom, Iso.app_inv, NatIso.mapHomologicalComplex_hom_app_f,
      NatIso.mapHomologicalComplex_inv_app_f, Q] using hv m
  choose w hw using hlift
  have hnm (m n : ℤ) (h : (ComplexShape.up ℤ).Rel n m) : n = m - 1 := by
    change n + 1 = m at h
    omega
  let z (m n : ℤ) (h : (ComplexShape.up ℤ).Rel n m) :
      (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (E₀.X m) ⟶
        (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (K₀.X n) :=
    w m ≫ eqToHom (congrArg
      (fun n ↦ (ModuleCat.extendScalars (F.map (homOfLE t.property)).hom).obj (K₀.X n))
      (hnm m n h).symm)
  refine ⟨t, hik, z, ?_⟩
  dsimp only
  intro m n h
  have hn := hnm m n h
  subst n
  simpa only [z, eqToHom_refl, Category.comp_id, e, Iso.trans_hom, Iso.trans_inv,
    HomologicalComplex.comp_f, eqToIso.hom, eqToIso.inv, HomologicalComplex.eqToHom_f,
    Iso.app_hom, Iso.app_inv, NatIso.mapHomologicalComplex_hom_app_f,
    NatIso.mapHomologicalComplex_inv_app_f, Category.assoc] using hw m

end CochainComplex
