/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionFiniteGluing
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# A finite flat model for depth-three punctured lifting

## References

* Stacks Project, proof of Tag 0BLS through Tags 0BLL, 0BLH, 0BM6 and 09ZL
* Stacks Project, Tag 0AVY
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Construct a compatible finite flat model with etale principal quotient. -/
theorem exists_finite_flat_model_of_depth_three_of_quotient_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q] [Etale q]
    (hquot :
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
      let V := i ⁻¹ᵁ U
      ∃ (F₀ : Scheme.{u}) (r₀ : F₀ ⟶ Spec (.of (A ⧸ Ideal.span {f}))),
        IsFinite r₀ ∧ Etale r₀ ∧
          ∃ e₀ : pullback q (i ∣_ U) ≅ (r₀ ⁻¹ᵁ V).toScheme,
            e₀.hom ≫ r₀ ∣_ V = pullback.snd q (i ∣_ U)) :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧ Flat r ∧
      Etale (pullback.snd r
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f}))))) ∧
      ∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let c := Spec.map (CommRingCat.ofHom (algebraMap A C))
  obtain ⟨E, s, hfiniteE, hetaleE, hext⟩ :=
    exists_completed_etale_extension_of_depth_three_of_quotient_extension
      A f hf hdepth U hU q hquot
  let : IsFinite s := hfiniteE
  let : Etale s := hetaleE
  obtain ⟨F, r, hfinite, he, eC, heC⟩ :=
    exists_finite_model_of_completed_model A U hU q E s hext
  let : Module.FaithfullyFlat A C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hff := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A C))).mpr
      ((RingHom.faithfullyFlat_algebraMap_iff (R := A) (S := C)).mpr inferInstance)
  let : Flat c := hff.1
  let : Surjective c := hff.2
  have hbase : Etale (pullback.snd r c) := by
    rw [← heC]
    infer_instance
  have hetale : Etale r :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hbase
  let : Etale r := hetale
  exact ⟨F, r, hfinite, inferInstance, inferInstance, he⟩

end AlgebraicGeometry.Scheme
