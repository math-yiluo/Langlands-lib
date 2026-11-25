/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Unramifiedness detected on a principal quotient of a local base

## References

* Stacks Project, Tag 02GU, differential criterion, and Nakayama's lemma (00DV)
* Stacks Project, Tag 02GU (differential criterion), and Tag 00DV (Nakayama)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

private theorem algebra_unramified_of_quotient
    (A B : Type u) [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A)
    [Algebra.FormallyUnramified (A ⧸ I) ((A ⧸ I) ⊗[A] B)] :
    Algebra.FormallyUnramified A B := by
  constructor
  let : Algebra B ((A ⧸ I) ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : Subsingleton ((A ⧸ I) ⊗[A] Ω[B⁄A]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase A (A ⧸ I) B ((A ⧸ I) ⊗[A] B)).subsingleton
  have : Subsingleton (Ω[B⁄A] ⧸ (I • (⊤ : Submodule A Ω[B⁄A]))) :=
    (TensorProduct.quotTensorEquivQuotSMul Ω[B⁄A] I).symm.injective.subsingleton
  have hle : (⊤ : Submodule A Ω[B⁄A]) ≤ I • ⊤ := by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ 0)
  have : Module.Finite A Ω[B⁄A] := Module.Finite.trans B Ω[B⁄A]
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I
    (⊤ : Submodule A Ω[B⁄A]) Module.Finite.fg_top hle
    (hI.trans (IsLocalRing.maximalIdeal_le_jacobson _))
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hx : x ∈ (⊥ : Submodule A Ω[B⁄A]) := hbot ▸ Submodule.mem_top
  simpa using hx

/-- A finite morphism over a local ring is formally unramified if its principal
quotient is etale and the defining element belongs to the maximal ideal. -/
theorem formallyUnramified_of_finite_of_principal_quotient_etale
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    {F : Scheme.{u}} (r : F ⟶ Spec (.of A)) [IsFinite r]
    (hquot : Etale (pullback.snd r
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))))) :
    FormallyUnramified r := by
  have : IsAffine F := isAffine_of_isAffineHom r
  wlog hF : ∃ B : CommRingCat.{u}, F = Spec B generalizing F
  · rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := @FormallyUnramified) F.isoSpec.inv]
    have heq :
        pullback.snd (F.isoSpec.inv ≫ r)
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) =
        pullback.map _ _ _ _ F.isoSpec.inv (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
          pullback.snd r
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) :=
      (pullback.lift_snd _ _ _).symm
    have hq : Etale (pullback.snd (F.isoSpec.inv ≫ r)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))) := by
      rw [heq, MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]
      exact hquot
    exact this (F.isoSpec.inv ≫ r) hq (by infer_instance) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hF
  obtain ⟨φ, rfl⟩ := Spec.map_surjective r
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  algebraize [φ.hom]
  let I : Ideal A := Ideal.span {f}
  let i : Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : Module.Finite A B := (IsFinite.SpecMap_iff φ).mp inferInstance
  have : Etale (pullback.snd (Spec.map φ) i) := hquot
  have hq : Etale (pullback.fst i (Spec.map φ)) := by
    have hh : Etale ((pullbackSymmetry i (Spec.map φ)).hom ≫
        pullback.snd (Spec.map φ) i) := inferInstance
    simpa using hh
  have he : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)))) := by
    rw [← pullbackSpecIso_inv_fst' A (A ⧸ I) B]
    infer_instance
  have : Algebra.FormallyUnramified (A ⧸ I) ((A ⧸ I) ⊗[A] B) :=
    RingHom.formallyUnramified_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp he).formallyUnramified
  change Algebra.FormallyUnramified A B
  exact algebra_unramified_of_quotient A B I
    (Ideal.span_le.mpr (by simpa using hf))

end AlgebraicGeometry.Scheme
