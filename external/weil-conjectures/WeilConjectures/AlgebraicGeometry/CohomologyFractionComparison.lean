/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.CohomologySectionDivision

/-! # Comparison from cohomology fractions

Source: Stacks Project, Tag 09MR, Mayer--Vietoris paragraph.
(blueprint: lem-sc-cohomology-fraction-comparison)
-/

@[expose] public section

universe uMV

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- Restriction to the nonvanishing open followed by division by the section descends
through the explicit fraction relations, simultaneously on every open and in every degree.
No assertion of exactness or bijectivity is made.

Source: Stacks Project, Tag 09MR, canonical map preceding the proof.
Proof: On S the section s is a free generator of L (Tag 01CY). Hence multiplication
by its n-th tensor power identifies the restricted F with the restricted n-th twist.
Restrict cohomology classes to W intersect S and apply the inverse of this identification.
These additive maps from each summand extend to the direct sum. Multiplication by s^b
followed by division by s^(n+b) is division by s^n, so each generating relation maps
to zero. Their additive closure also maps to zero. The quotient universal property
therefore gives c. Applying multiplication by s^n cancels its inverse and gives the
asserted formula. This construction works without compactness or quasi-coherence;
for an empty nonvanishing open the target is zero, and for n=0 it is restriction.
(blueprint: lem-sc-cohomology-fraction-comparison). -/
theorem exists_cohomologyFraction_comparison (X : Scheme.{uMV}) (L F : X.Modules) [L.IsInvertible]
    (s : Γ(L, ⊤))
    (S : X.Opens) (_hS : (S : Set X) = nonvanishingLocus L s) :
    ∃ c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F,
      (∀ (W : X.Opens) (p n : ℕ)
        (ξ : (openModuleCohomology X.toRingedSpace p W).obj (F ⊗ L.tensorPow n : X.Modules)),
        (openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (c W p (cohomologyFraction L F s p W n ξ)) =
          (openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app (F ⊗ L.tensorPow n : X.Modules) ξ) := by
  classical
  obtain ⟨q, hq, htransition, -⟩ := exists_cohomologySection_division X L F s S _hS
  let f (W : X.Opens) (p : ℕ) := DirectSum.toAddMonoid (q W p)
  have hf (W : X.Opens) (p : ℕ) :
      cohomologyFractionRelations L F s p W ≤ (f W p).ker := by
    unfold cohomologyFractionRelations
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨n, b, ξ, rfl⟩
    change (f W p) (_ - _) = 0
    simp only [map_sub, f, DirectSum.toAddMonoid_of]
    exact sub_eq_zero.mpr (htransition W p n b ξ).symm
  let c (W : X.Opens) (p : ℕ) :=
    QuotientAddGroup.lift (cohomologyFractionRelations L F s p W) (f W p) (hf W p)
  refine ⟨c, ?_⟩
  intro W p n ξ
  have hval : c W p (cohomologyFraction L F s p W n ξ) = q W p n ξ := by
    simp only [c, cohomologyFraction, QuotientAddGroup.lift_mk', f,
      DirectSum.toAddMonoid_of]
  rw [hval]
  exact hq W p n ξ

end AlgebraicGeometry
