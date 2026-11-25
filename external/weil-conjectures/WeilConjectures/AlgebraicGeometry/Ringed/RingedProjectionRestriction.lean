/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalModel
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso

/-! # Canonical localization comparisons for the projection mate

## References

* Stacks 04J0, 08FI, 0FN5, 07A4, 0B56 and 0944
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
/-- Canonical localization comparisons for the projection mate on ringed pro-etale sites. -/
theorem ringedProjectionRestriction
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X) :
    ∃ g : Global f R_Y R_X c,
      ∃ data : ∀ V : Y.ProEt, Local f R_Y R_X c g V,
        (∀ V : Y.ProEt, (data V).ProjectionCompatible) ∧
        (∀ {A B : Der R_Y} (a : A ⟶ B),
          (∀ V : Y.ProEt, ∃ S : Sieve V, S ∈ ProEt.topology Y V ∧
            ∀ (W : Y.ProEt) (h : W ⟶ V), S.arrows h →
              IsIso (((data W).restrictionY.model).functor.map a)) → IsIso a) := by
  classical
  obtain ⟨g⟩ := ProjectionRestriction.globalModel_exists f R_Y R_X c
  have hl := fun V ↦ ProjectionRestriction.localModel_exists f R_Y R_X c g V
  choose data hd using hl
  refine ⟨g, data, hd, ?_⟩
  intro A B a ha
  apply SheafOfModules.ringedRestrictionLocalIso
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R_Y) a
  intro V
  obtain ⟨S, hS, h⟩ := ha V
  refine ⟨S, hS, ?_⟩
  intro W f hf
  let r := (data W).restrictionY
  let := r.additive
  let := r.limits
  let := r.colimits
  exact h W f hf
end AlgebraicGeometry.Scheme
