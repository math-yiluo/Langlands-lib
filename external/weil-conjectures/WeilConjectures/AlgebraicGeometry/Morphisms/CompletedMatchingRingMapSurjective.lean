/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapResidueLift
import Mathlib.RingTheory.Nakayama

/-! # Surjectiveity of completed matching sections

## References

* Stacks Project, Tag 05ER, cokernel argument
* Tags 0BLH and 05EU
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed matching-ring comparison is surjective. -/
theorem completedRingMap_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    Function.Surjective D.completedRingMap := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let g : CommRingCat.of C ⟶ Γ(E, ⊤) := (ΓSpecIso (.of C)).inv ≫ s.appTop
  let P : CommRingCat.{u} := pushout D.baseMap (CommRingCat.ofHom (algebraMap A C))
  let j := pushout.inr D.baseMap (CommRingCat.ofHom (algebraMap A C))
  let := g.hom.toAlgebra
  let := j.hom.toAlgebra
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
  have hg : g.hom.Finite := s.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      ((ConcreteCategory.isIso_iff_bijective (ΓSpecIso (.of C)).inv).mp
        (by infer_instance)).2)
  let : Module.Finite C Γ(E, ⊤) := hg
  apply F.surjective_of_surjective_comp_mkQ (IsLocalRing.maximalIdeal C)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro z
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective
    ((IsLocalRing.maximalIdeal C) • (⊤ : Submodule C Γ(E, ⊤))) z
  obtain ⟨a, ha⟩ := D.completedRingMap_residue_lift hU b
  refine ⟨a, ?_⟩
  change Submodule.Quotient.mk (F a) = Submodule.Quotient.mk b
  apply (Submodule.Quotient.eq _).mpr
  rw [Ideal.smul_top_eq_map]
  exact ha

end AlgebraicGeometry.Scheme.CompletionGluingData
