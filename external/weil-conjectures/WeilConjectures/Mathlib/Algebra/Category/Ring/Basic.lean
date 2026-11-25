/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Ideals and isomorphisms of `CommRingCat`

`Ideal.comap_symm` in the language of isomorphisms in `CommRingCat`, and the instance saying
that `CommRingCat.ofHom` of a ring isomorphism is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory

/-- Pullback of an ideal along the inverse of an isomorphism of commutative rings is
pushforward along the isomorphism. -/
lemma CommRingCat.comap_inv_eq_map {R S : CommRingCat.{u}} (e : R ≅ S) (I : Ideal R) :
    I.comap e.inv.hom = I.map e.hom.hom :=
  Ideal.comap_symm e.commRingCatIsoToRingEquiv

/-- `CommRingCat.ofHom` of a ring isomorphism is an isomorphism in `CommRingCat`. -/
instance CommRingCat.isIso_ofHom_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) : IsIso (CommRingCat.ofHom e.toRingHom) :=
  e.toCommRingCatIso.isIso_hom
