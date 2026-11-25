/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.FormalGlueingH0PrimeSpan
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingData

/-! # Surjectivity of the completed comparison on residue quotients

## References

* Stacks Project, Tags 0BLH and 05ER
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed comparison is onto after passage to the residue quotient. -/
theorem completedRingMap_residue_quotient_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    let P : CommRingCat := pushout D.baseMap (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
    Function.Surjective (fun a : P =>
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A)).map
          (((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
            s.appTop).hom)) (D.completedRingMap a)) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
  let P : CommRingCat := pushout D.baseMap (CommRingCat.ofHom (algebraMap A C))
  let j := pushout.inr D.baseMap (CommRingCat.ofHom (algebraMap A C))
  let : Module C Γ(E, ⊤) := Module.compHom _ g.hom
  let : Algebra C P := j.hom.toAlgebra
  let F : P →ₗ[C] Γ(E, ⊤) :=
    { toFun := D.completedRingMap
      map_add' := map_add D.completedRingMap.hom
      map_smul' := by
        intro c a
        change D.completedRingMap (j c * a) = g c * D.completedRingMap a
        rw [map_mul]
        congr 1
        exact congrArg (fun k : CommRingCat.of C ⟶ Γ(E, ⊤) ↦ k c)
          (show j ≫ D.completedRingMap = g by
            simp only [j, completedRingMap, pushout.inr_desc, g, C]) }
  obtain ⟨t, f, hgen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
  change Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A at hgen
  have hflat : (algebraMap A C).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hquot : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap A C))
      (algebraMap A C) Ideal.le_comap_map) := by
    have hres (J : Ideal C) (hJ : J = IsLocalRing.maximalIdeal C)
        (h : IsLocalRing.maximalIdeal A ≤ J.comap (algebraMap A C)) :
        Function.Bijective (Ideal.quotientMap J (algebraMap A C) h) := by
      subst J
      exact AdicCompletion.residueField_map_bijective A
    rw [hgen]
    exact hres _ AdicCompletion.maximalIdeal_eq_map.symm Ideal.le_comap_map
  obtain ⟨X, e, k, hk⟩ :=
    D.exists_formalGlueingData_matching_projection hU t f hgen
  have hspan := FormalGlueing.h0_prime_span_eq_top (algebraMap A C) t f hflat hquot X
  have hle : Submodule.span C
      (Set.range (fun h : FormalGlueing.h0 (algebraMap A C) f X ↦
        (h.val.1 : X.M'))) ≤ (LinearMap.range F).comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    refine ⟨pushout.inl D.baseMap (CommRingCat.ofHom (algebraMap A C)) (k h), ?_⟩
    change D.completedRingMap
      (pushout.inl D.baseMap (CommRingCat.ofHom (algebraMap A C)) (k h)) = _
    have heq := congrArg (fun v : D.matchingRing ⟶ Γ(E, ⊤) ↦ v (k h))
      (pushout.inl_desc
        (pullback.snd (pullback.fst q (completionSpecMap A ∣_ U)).appTop
          D.toCompleted.appTop) g D.completedRingMap_condition)
    exact heq.trans (hk h)
  rw [hspan] at hle
  have hsurj : Function.Surjective D.completedRingMap := by
    intro b
    obtain ⟨x, rfl⟩ := e.surjective b
    exact hle (Submodule.mem_top : x ∈ (⊤ : Submodule C X.M'))
  exact (Ideal.Quotient.mk_surjective).comp hsurj

end AlgebraicGeometry.Scheme.CompletionGluingData
