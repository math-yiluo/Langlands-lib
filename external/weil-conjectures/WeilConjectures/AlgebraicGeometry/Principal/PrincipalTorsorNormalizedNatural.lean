/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorSignedRepresentatives
/-! Independent comparison result for the principal torsor sign calculation.

## References

* Stacks 03AJ, 0G78
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- Cocycle-normalized supported-Hom comparisons are natural in coefficient lifts and
etale restriction. -/
theorem principalTorsorNormalizedNatural
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) : C.Natural := by
  refine ⟨?_, ?_⟩
  · intro T Z i _ W h G G' a I J f hf q x
    obtain ⟨z, hz, rfl⟩ := I.extMk_surjective x (q + 1 + 1) rfl
    rw [InjectiveResolution.extMk_comp_mk₀ z _ rfl hz (⟨f, by simpa using hf⟩ : I.Hom J a)]
    refine (hC.2.2 T Z i W h G' J q _ _).unique ?_
    have hm := (hC.2.2 T Z i W h G I q z hz).map _ _ (relativeSectionMap_square T _ f)
    rw [map_zero] at hm
    exact hm
  · intro T Z T' Z' v _ i _ i' _ w _ W h h' G G' I J f q z hz z' hz' hres
    refine (hC.2.2 T' Z' i' (v ⁻¹ᵁ W) h' G' J q z' hz').unique ?_
    rw [hres]
    have hm := (hC.2.2 T Z i W h G I q z hz).map _ _ (relativeTransfer_square v W _ _ f)
    rw [map_zero] at hm
    exact hm
end AlgebraicGeometry.Etale
