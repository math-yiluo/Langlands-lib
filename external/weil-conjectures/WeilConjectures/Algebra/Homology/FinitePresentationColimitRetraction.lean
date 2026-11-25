/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.FinitePresentationMapCanonical
import WeilConjectures.Algebra.Homology.PreorderModuleMapEqualityDescent

/-! # Descent of a retraction between fixed finitely presented models

Source: Stacks Project, More on Algebra, Tag 0BC7, first proof paragraph,
using Algebra, Tag 05N7, map and equality clauses.
(blueprint: lem-pc-fp-colimit-retraction).
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
    let c := eqToIso (congrArg extendScalars hp) ≪≫ extendScalarsComp p q
    (ej M).hom ≫ (extendScalars rj).map (c.hom.app M ≫ (extendScalars q).map v ≫ c.inv.app N) ≫
        (ej N).inv =
      (ei M).hom ≫ (extendScalars ri).map v ≫ (ei N).inv := by
  subst p'
  subst ri
  subst r0
  simpa [eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Iso.trans_hom, Iso.trans_inv,
    Category.id_comp, Category.comp_id, Iso.app_hom, Iso.app_inv] using transport p q rj M N v

private theorem finitePresentation_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Module.FinitePresentation S ((extendScalars r).obj M) := by
  let := r.toAlgebra
  change Module.FinitePresentation S (TensorProduct R S M)
  infer_instance

private theorem retraction_of_conjugation
    {C D : Type u} [Category C] [Category D] (T : C ⥤ D)
    {M N : C} {X Y : D} (eM : X ≅ T.obj M) (eN : Y ≅ T.obj N)
    (s : M ⟶ N) (r : N ⟶ M)
    (h : (eM.hom ≫ T.map s ≫ eN.inv) ≫
      (eN.hom ≫ T.map r ≫ eM.inv) = 𝟙 _) :
    T.map (s ≫ r) = T.map (𝟙 M) := by
  rw [T.map_id]
  have h' := congrArg (fun f ↦ eM.inv ≫ f ≫ eM.hom) h
  simpa only [Functor.map_comp, Functor.map_id, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Category.comp_id,
    Category.id_comp, Iso.inv_hom_id] using h'

private theorem conjugation_retraction
    {C D : Type u} [Category C] [Category D] (T : C ⥤ D)
    {M N : C} {X Y : D} (eM : X ≅ T.obj M) (eN : Y ≅ T.obj N)
    (s : M ⟶ N) (r : N ⟶ M) (h : T.map (s ≫ r) = T.map (𝟙 M)) :
    (eM.hom ≫ T.map s ≫ eN.inv) ≫
      (eN.hom ≫ T.map r ≫ eM.inv) = 𝟙 _ := by
  rw [T.map_comp, T.map_id] at h
  have h' : T.map s ≫ T.map r = 𝟙 _ := by
    simpa only [Functor.map_comp, Functor.map_id] using h
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (T.map s), h']
  simp


/-- A retraction between two fixed finitely presented models descends to a later stage.
Source: Stacks Project, More on Algebra, Tag 0BC7, label lemma-colimit-perfect,
first proof paragraph, using Algebra, Tag 05N7, (2) and (3).
(blueprint: lem-pc-fp-colimit-retraction).

Proof: Replace the directed preorder by its antisymmetrization and transport the ring
colimit and the fixed models along the equivalence of indexing categories. Apply the
map clause of finitePresentation_descent_directedColimit separately to s and r.
Directedness supplies a common stage above both stages; extend both maps to that
stage. Use extendScalarsComp and cocone naturality to identify their further scalar
extensions with s and r. The comparison isomorphisms in the map clause agree with
these canonical ones because they agree on all tensors 1 tensor m, which generate
the base changes. Thus the composite of the two descended maps becomes the identity
after extending to the colimit. Finite presentation is preserved by scalar extension.
Apply the equality clause to this composite and the identity, then extend both maps
to the resulting later stage. Functoriality makes their composite the identity there,
and the canonical iterated scalar-extension isomorphisms carry their extensions to the
colimit to s and r. Lift this stage and these maps back to the original preorder.
For zero models the maps are zero and
the identity of the zero module is zero; for a singleton diagram this is ordinary
transport of a retraction along a ring isomorphism. -/
theorem exists_retraction_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (i : I) (M N : ModuleCat.{u} (F.obj i))
    (hM : Module.FinitePresentation (F.obj i) M)
    (hN : Module.FinitePresentation (F.obj i) N)
    (s : (extendScalars (colimit.ι F i).hom).obj M ⟶
      (extendScalars (colimit.ι F i).hom).obj N)
    (r : (extendScalars (colimit.ι F i).hom).obj N ⟶
      (extendScalars (colimit.ι F i).hom).obj M)
    (hsr : s ≫ r = 𝟙 _) :
    ∃ (j : I) (hij : i ≤ j),
      let E := extendScalars (F.map (homOfLE hij)).hom
      let e (X : ModuleCat.{u} (F.obj i)) := eqToIso (congrArg (fun r ↦ (extendScalars r).obj X)
          (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hij)).symm)) ≪≫
        (extendScalarsComp (F.map (homOfLE hij)).hom (colimit.ι F j).hom).app X
      ∃ (s' : E.obj M ⟶ E.obj N) (r' : E.obj N ⟶ E.obj M),
        s' ≫ r' = 𝟙 _ ∧
        (e M).hom ≫ (extendScalars (colimit.ι F j).hom).map s' ≫ (e N).inv = s ∧
        (e N).hom ≫ (extendScalars (colimit.ι F j).hom).map r' ≫ (e M).inv = r := by
  classical
  let e (t : Set.Ici i) (X : ModuleCat.{u} (F.obj i)) :=
    eqToIso (congrArg (fun r ↦ (extendScalars r).obj X)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
    (extendScalarsComp (F.map (homOfLE t.property)).hom (colimit.ι F t.val).hom).app X
  obtain ⟨a, sa, hsa⟩ := finitePresentation_map_directedColimit F i M N hM hN s
  obtain ⟨b, rb, hrb⟩ := finitePresentation_map_directedColimit F i N M hN hM r
  obtain ⟨j, haj, hbj⟩ := exists_ge_ge a.val b.val
  let t : Set.Ici i := ⟨j, a.property.trans haj⟩
  have lift (a : Set.Ici i) (haj : a.val ≤ j) (X Y : ModuleCat.{u} (F.obj i))
      (v : (extendScalars (F.map (homOfLE a.property)).hom).obj X ⟶
        (extendScalars (F.map (homOfLE a.property)).hom).obj Y) :
      ∃ w : (extendScalars (F.map (homOfLE t.property)).hom).obj X ⟶
        (extendScalars (F.map (homOfLE t.property)).hom).obj Y,
        (e t X).hom ≫ (extendScalars (colimit.ι F j).hom).map w ≫ (e t Y).inv =
          (e a X).hom ≫ (extendScalars (colimit.ι F a.val).hom).map v ≫ (e a Y).inv :=
    ⟨_, transportComparisons
      (F.map (homOfLE a.property)).hom (F.map (homOfLE t.property)).hom
      (F.map (homOfLE haj)).hom (colimit.ι F a.val).hom
      (colimit.ι F j).hom (colimit.ι F i).hom
      (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE a.property) (homOfLE haj)))
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE haj))).symm
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE a.property))).symm
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property))).symm X Y v⟩
  obtain ⟨sj, hsj⟩ := lift a haj M N sa
  obtain ⟨rj, hrj⟩ := lift b hbj N M rb
  have hs : (e t M).hom ≫ (extendScalars (colimit.ι F j).hom).map sj ≫
      (e t N).inv = s := hsj.trans hsa
  have hr : (e t N).hom ≫ (extendScalars (colimit.ι F j).hom).map rj ≫
      (e t M).inv = r := hrj.trans hrb
  let E := extendScalars (F.map (homOfLE t.property)).hom
  let A := extendScalars (colimit.ι F j).hom
  have heq : A.map (sj ≫ rj) = A.map (𝟙 (E.obj M)) := by
    apply retraction_of_conjugation A (e t M) (e t N) sj rj
    rw [hs, hr]
    exact hsr
  have : Module.FinitePresentation (F.obj i) M := hM
  obtain ⟨k, hjk, hk⟩ := eventually_equal_maps_of_directed_preorder_colimit
    F j (E.obj M) (E.obj M) (finitePresentation_extendScalars _ _)
      (finitePresentation_extendScalars _ _) (sj ≫ rj) (𝟙 _) heq
  let T := extendScalars (F.map (homOfLE hjk)).hom
  have hc : (F.map (homOfLE (t.property.trans hjk))).hom =
      (F.map (homOfLE hjk)).hom.comp (F.map (homOfLE t.property)).hom :=
    congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE t.property) (homOfLE hjk))
  let c := eqToIso (congrArg extendScalars hc) ≪≫
    extendScalarsComp (F.map (homOfLE t.property)).hom (F.map (homOfLE hjk)).hom
  have move (X Y : ModuleCat.{u} (F.obj i)) (v : E.obj X ⟶ E.obj Y) :=
    transportComparisons
      (F.map (homOfLE t.property)).hom (F.map (homOfLE (t.property.trans hjk))).hom
      (F.map (homOfLE hjk)).hom (colimit.ι F j).hom
      (colimit.ι F k).hom (colimit.ι F i).hom hc
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hjk))).symm
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property))).symm
      (congrArg CommRingCat.Hom.hom
        (colimit.w F (homOfLE (t.property.trans hjk)))).symm X Y v
  refine ⟨k, t.property.trans hjk,
    c.hom.app M ≫ T.map sj ≫ c.inv.app N,
    c.hom.app N ≫ T.map rj ≫ c.inv.app M, ?_, (move M N sj).trans hs,
    (move N M rj).trans hr⟩
  exact conjugation_retraction T (c.app M) (c.app N) sj rj hk

end ModuleCat
