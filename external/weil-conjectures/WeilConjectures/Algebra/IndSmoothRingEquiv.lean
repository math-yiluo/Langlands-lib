/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.RingHom.Smooth

@[expose] public section

universe u v w

open CategoryTheory

namespace Algebra

private def scalarFunctor {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CommAlgCat.{v} S ⥤ CommAlgCat.{v} R where
  obj A :=
    letI : Algebra R A := Algebra.compHom A e.toRingHom
    CommAlgCat.of R A
  map {A B} g :=
    letI : Algebra R A := Algebra.compHom A e.toRingHom
    letI : Algebra R B := Algebra.compHom B e.toRingHom
    CommAlgCat.ofHom
      { g.hom.toRingHom with
        commutes' r := g.hom.commutes (e r) }

private def scalarEquivalence {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CommAlgCat.{v} S ≌ CommAlgCat.{v} R where
  functor := scalarFunctor e
  inverse := scalarFunctor e.symm
  unitIso := NatIso.ofComponents fun A ↦ CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv S A A _ _ _ A.algebra
      (@Algebra.compHom R S A _ _ _ (Algebra.compHom A e.toRingHom) e.symm.toRingHom)
      (RingEquiv.refl A) fun r ↦ by
        change algebraMap S A r = algebraMap S A (e (e.symm r))
        simp
  counitIso := NatIso.ofComponents fun A ↦ CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv R A A _ _ _
      (@Algebra.compHom S R A _ _ _ (Algebra.compHom A e.symm.toRingHom) e.toRingHom)
      A.algebra (RingEquiv.refl A) fun r ↦ by
        change algebraMap R A (e.symm (e r)) = algebraMap R A r
        simp

/-- Ind-smoothness transports across compatible ring isomorphisms.

Source: the scalar transport argument in Stacks Project, Smoothing Ring Maps, Tag 07CM.
Restrict scalars along the base isomorphism; its inverse supplies an inverse functor.
Map the filtered colimit presentation through this equivalence. Each term stays smooth
because its structure homomorphism is composed with a ring isomorphism. Finally use the
compatible algebra isomorphism to change the vertex.
(blueprint: lem-weil-pbc-ind-smooth-ring-equiv) -/
theorem ind_smooth_of_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    {A B : Type v} [CommRing A] [CommRing B] [Algebra S A] [Algebra R B]
    (e : R ≃+* S) (f : A ≃+* B)
    (hf : ∀ r, f (algebraMap S A (e r)) = algebraMap R B r)
    (hA : ObjectProperty.ind.{w} (fun C : CommAlgCat.{v} S ↦ Smooth S C)
      (CommAlgCat.of S A)) :
    ObjectProperty.ind.{w} (fun C : CommAlgCat.{v} R ↦ Smooth R C)
      (CommAlgCat.of R B) := by
  obtain ⟨J, _, _, pres, hp⟩ := hA
  let F := scalarEquivalence.{u, v} e
  have hterms (j : J) : Smooth R (F.functor.obj (pres.diag.obj j)) := by
    let : Algebra R (pres.diag.obj j) := Algebra.compHom _ e.toRingHom
    change Smooth R (pres.diag.obj j)
    apply RingHom.smooth_algebraMap.mp
    exact (RingHom.Smooth.of_bijective e.bijective).comp
      (RingHom.smooth_algebraMap.mpr (hp j))
  have hX : ObjectProperty.ind.{w} (fun C : CommAlgCat.{v} R ↦ Smooth R C)
      (F.functor.obj (CommAlgCat.of S A)) :=
    ⟨J, inferInstance, inferInstance, pres.map F.functor, hterms⟩
  let iso : F.functor.obj (CommAlgCat.of S A) ≅ CommAlgCat.of R B :=
    by
      letI : Algebra R A := Algebra.compHom A e.toRingHom
      exact CommAlgCat.isoMk { toRingEquiv := f, commutes' := hf }
  exact ObjectProperty.prop_of_iso (ObjectProperty.ind _) iso hX

end Algebra
