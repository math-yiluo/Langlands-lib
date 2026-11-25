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
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Order.Antisymmetrization
import WeilConjectures.Algebra.FinitePresentationColimit

/-! # Equality descent for module maps over a directed preorder

Source: Stacks Project, Algebra, Tag 05N7 (3).
(blueprint: lem-pc-preorder-module-map-equality-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem scalarExtension_map_eq_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (r : R →+* S) (s : S →+* T) (M N : ModuleCat.{u} R) (f g : M ⟶ N) :
    (extendScalars (s.comp r)).map f = (extendScalars (s.comp r)).map g ↔
      (extendScalars s).map ((extendScalars r).map f) =
        (extendScalars s).map ((extendScalars r).map g) := by
  let e := extendScalarsComp r s
  constructor
  · intro h
    change (extendScalars r ⋙ extendScalars s).map f =
      (extendScalars r ⋙ extendScalars s).map g
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g]
    exact congrArg (fun t ↦ e.inv.app M ≫ t ≫ e.hom.app N) h
  · intro h
    rw [← NatIso.naturality_2 e f, ← NatIso.naturality_2 e g]
    exact congrArg (fun t ↦ e.hom.app M ≫ t ≫ e.inv.app N) h

private theorem scalarExtension_map_eq_reflect
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S) (s : S →+* R)
    (hrs : s.comp r = RingHom.id R) (M N : ModuleCat.{u} R) (f g : M ⟶ N)
    (h : (extendScalars r).map f = (extendScalars r).map g) : f = g := by
  have h' := (scalarExtension_map_eq_comp r s M N f g).mpr
    (congrArg (fun t ↦ (extendScalars s).map t) h)
  rw [hrs] at h'
  let e := extendScalarsId R
  rw [← NatIso.naturality_2 e f, ← NatIso.naturality_2 e g] at h'
  simpa only [Functor.id_map, cancel_epi, cancel_mono] using h'

private theorem finitePresentation_extendScalars
    {R S : Type u} [CommRing R] [CommRing S] (r : R →+* S)
    (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Module.FinitePresentation S ((extendScalars r).obj M) := by
  let := r.toAlgebra
  change Module.FinitePresentation S (TensorProduct R S M)
  infer_instance

/-- Equality of maps between finitely presented modules is detected at a later stage.
Source: Stacks Project, Algebra, Tag 05N7 (3).

Proof: Let J be the antisymmetrization of I, and H : J → I a monotone choice
of representatives. J is a nonempty directed partial order, and H is final because
every index lies below its representative. Hence c : colimit (H ⋙ F) → colimit F
is an isomorphism. Extend M,N and f,g from i to the representative p of i. They
remain finitely presented, and functoriality of the colimit cocone and naturality of
extendScalarsComp identify their extensions to colimit F with those of f,g. Their
extensions to colimit (H ⋙ F) also agree: extension along the isomorphism c reflects
equality, as extension along its inverse and extendScalarsId recover the original
maps. Apply the equality clause of finitePresentation_descent_directedColimit to
H ⋙ F at the class of i. Its later quotient index j gives p ≤ H(j), hence i ≤ H(j).
Naturality of extendScalarsComp identifies the iterated extension of f,g through p
with direct extension from i to H(j), proving the result. This includes mutually
comparable distinct indices, equal maps, and zero modules; i ensures nonemptiness.
(blueprint: lem-pc-preorder-module-map-equality-descent) -/
theorem eventually_equal_maps_of_directed_preorder_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i : I) (M N : ModuleCat.{u} (F.obj i))
    (hM : Module.FinitePresentation (F.obj i) M)
    (hN : Module.FinitePresentation (F.obj i) N) (f g : M ⟶ N)
    (h : (extendScalars (colimit.ι F i).hom).map f =
      (extendScalars (colimit.ι F i).hom).map g) :
    ∃ (j : I) (hij : i ≤ j),
      (extendScalars (F.map (homOfLE hij)).hom).map f =
        (extendScalars (F.map (homOfLE hij)).hom).map g := by
  classical
  have : Nonempty I := ⟨i⟩
  let J := Antisymmetrization I (· ≤ ·)
  let q : I → J := toAntisymmetrization (· ≤ ·)
  let H : J ⥤ I := (OrderEmbedding.ofAntisymmetrization (α := I)).monotone.functor
  have hrep (x : I) : x ≤ H.obj (q x) := by
    apply toAntisymmetrization_le_toAntisymmetrization_iff.mp
    change toAntisymmetrization (· ≤ ·) x ≤
      toAntisymmetrization (· ≤ ·) (ofAntisymmetrization (· ≤ ·) (q x))
    rw [toAntisymmetrization_ofAntisymmetrization]
  have : Nonempty J := ⟨q i⟩
  have : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge (H.obj a) (H.obj b)
    refine ⟨q k, ?_, ?_⟩
    · change ofAntisymmetrization (· ≤ ·) a ≤ k at hak
      simpa only [toAntisymmetrization_ofAntisymmetrization] using
        toAntisymmetrization_mono hak
    · change ofAntisymmetrization (· ≤ ·) b ≤ k at hbk
      simpa only [toAntisymmetrization_ofAntisymmetrization] using
        toAntisymmetrization_mono hbk⟩
  have : H.Final := (OrderEmbedding.ofAntisymmetrization (α := I)).monotone.final_functor_iff.mpr
    (fun x ↦ ⟨q x, hrep x⟩)
  let G := H ⋙ F
  let p := H.obj (q i)
  let r := (F.map (homOfLE (hrep i))).hom
  let M' := (extendScalars r).obj M
  let N' := (extendScalars r).obj N
  let f' := (extendScalars r).map f
  let g' := (extendScalars r).map g
  have hF : (extendScalars (colimit.ι F p).hom).map f' =
      (extendScalars (colimit.ι F p).hom).map g' := by
    apply (scalarExtension_map_eq_comp r (colimit.ι F p).hom M N f g).mp
    have hr : (colimit.ι F p).hom.comp r = (colimit.ι F i).hom :=
      congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE (hrep i)))
    rw [hr]
    exact h
  let c := colimit.pre F H
  have hG : (extendScalars (colimit.ι G (q i)).hom).map f' =
      (extendScalars (colimit.ι G (q i)).hom).map g' := by
    apply scalarExtension_map_eq_reflect c.hom (inv c).hom
      (congrArg CommRingCat.Hom.hom (IsIso.hom_inv_id c))
      ((extendScalars (colimit.ι G (q i)).hom).obj M')
      ((extendScalars (colimit.ι G (q i)).hom).obj N')
    apply (scalarExtension_map_eq_comp (colimit.ι G (q i)).hom c.hom M' N' f' g').mp
    have hc : c.hom.comp (colimit.ι G (q i)).hom = (colimit.ι F p).hom :=
      congrArg CommRingCat.Hom.hom (colimit.ι_pre F H (q i))
    rw [hc]
    exact hF
  have hM' : Module.FinitePresentation (G.obj (q i)) M' := by
    have := hM
    exact finitePresentation_extendScalars r M
  have hN' : Module.FinitePresentation (G.obj (q i)) N' := by
    have := hN
    exact finitePresentation_extendScalars r N
  obtain ⟨j, hqij, hj⟩ := (finitePresentation_descent_directedColimit.{u, u, u, u} G).2.2
    (q i) M' N' hM' hN' f' g' hG
  have hpj : p ≤ H.obj j := H.monotone hqij
  refine ⟨H.obj j, (hrep i).trans hpj, ?_⟩
  have hr : (F.map (homOfLE ((hrep i).trans hpj))).hom =
      (F.map (homOfLE hpj)).hom.comp r :=
    congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE (hrep i)) (homOfLE hpj))
  rw [hr]
  apply (scalarExtension_map_eq_comp r (F.map (homOfLE hpj)).hom M N f g).mpr
  exact hj

end ModuleCat
