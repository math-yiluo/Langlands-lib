/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap
import WeilConjectures.AlgebraicGeometry.Morphisms.CompletedMatchingRingMapAwayOfPuncturedIso
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingPuncturedIso

/-! # Local torsion for the completed matching-ring kernel

## References

* Stacks Project, Tags 05ER and 05EC
* Stacks Project, Tag 05ER, second paragraph (05EP and 05EQ), applied to the affine charts in Tag
  0BLH
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Kernel elements are killed by powers of a finite set of maximal-ideal generators. -/
theorem completedRingMap_kernel_local_torsion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    ∀ x, D.completedRingMap x = 0 →
      ∃ (t : ℕ) (f : Fin t → A),
        IsLocalRing.maximalIdeal A = Ideal.span (Set.range f) ∧
          ∀ i, ∃ e : ℕ,
            ((D.baseMap ≫ pushout.inl _ _).hom (f i)) ^ e * x = 0 := by
  intro x hx
  have : IsIso D.puncturedMap := D.puncturedMap_isIso hU
  obtain ⟨t, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))
  refine ⟨t, f, hf.symm, ?_⟩
  intro i
  have hfi : f i ∈ IsLocalRing.maximalIdeal A := by
    rw [← hf]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hbasic : (PrimeSpectrum.basicOpen (f i) : (Spec (.of A)).Opens) ≤ U := by
    intro p hp
    apply (hU p).2
    intro heq
    subst p
    exact hp hfi
  have hbij := D.completedRingMap_away_bijective_of_puncturedMap_isIso (f i) hbasic
  exact Localization.awayMap_injective_iff.mp hbij.1 x hx

end AlgebraicGeometry.Scheme.CompletionGluingData
