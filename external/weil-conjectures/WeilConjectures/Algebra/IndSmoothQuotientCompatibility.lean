/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Smooth.Basic

import WeilConjectures.Algebra.IndSmoothRingEquiv

/-!
# Ind-smoothness and successive quotients

Source: Stacks Project, Smoothing Ring Maps, proof of Proposition Tag 07CM.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

/-- Taking a quotient by `K ≤ I` before reducing by `I` preserves the ind-smoothness
hypothesis on that reduction.

Source: Stacks Project, Smoothing Ring Maps, proof of Proposition Tag 07CM,
the induction on the nilpotence exponent
(blueprint: theorem-finite-etale-covers-proper-henselian--2).

Proof: Put `R' = R / K`, `Λ' = Λ / KΛ`, and `I' = I / K`. The third isomorphism
theorem identifies `R' / I'` with `R / I`. Since `KΛ ≤ IΛ`, it also identifies
`Λ' / I'Λ'` with `Λ / IΛ`. Both identifications send the class of an element to its
class, so they commute with the structure homomorphisms. Restriction along the base ring
isomorphism and its inverse gives inverse
equivalences of categories of commutative algebras. This preserves smoothness:
a finite polynomial presentation is transported by applying the base isomorphism
to its coefficients, and the lifting property for square-zero quotients is unchanged
when the scalar action is transported. The compatible vertex ring isomorphism is
then an algebra isomorphism over the transported base. Transport the filtered colimit presentation
in the hypothesis
through this equivalence and then through the compatible isomorphism of its vertex.
An equivalence preserves colimits, the indexing category is unchanged and remains
filtered, and the transported terms are smooth. This is the asserted presentation.
No nilpotence or flatness hypothesis is needed. -/
theorem ind_smooth_quotient_compatibility
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I K : Ideal R) (hKI : K ≤ I)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))) :
    let R' := R ⧸ K
    let Λ' := Λ ⧸ K.map (algebraMap R Λ)
    let I' := I.map (Ideal.Quotient.mk K)
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R' ⧸ I') ↦ Smooth (R' ⧸ I') C)
      (CommAlgCat.of (R' ⧸ I') (Λ' ⧸ I'.map (algebraMap R' Λ'))) := by
  dsimp
  let L := K.map (algebraMap R Λ)
  let J := I.map (algebraMap R Λ)
  have hLJ : L ≤ J := Ideal.map_mono hKI
  have hmap : (I.map (Ideal.Quotient.mk K)).map
      (algebraMap (R ⧸ K) (Λ ⧸ L)) = J.map (Ideal.Quotient.mk L) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
  let e := DoubleQuot.quotQuotEquivQuotOfLE hKI
  let f : ((Λ ⧸ L) ⧸ (I.map (Ideal.Quotient.mk K)).map
      (algebraMap (R ⧸ K) (Λ ⧸ L))) ≃+* Λ ⧸ J :=
    (Ideal.quotientEquivAlgOfEq Λ hmap).toRingEquiv.trans
      (DoubleQuot.quotQuotEquivQuotOfLE hLJ)
  apply ind_smooth_of_ringEquiv e f.symm _ hΛ
  intro r
  apply f.injective
  rw [f.apply_symm_apply]
  induction r using Quotient.inductionOn with
  | h r =>
    induction r using Quotient.inductionOn with
    | h r =>
      rfl


end Algebra
