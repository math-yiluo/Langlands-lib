/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityNormalBundle.PurityNormalBundle
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
import WeilConjectures.AlgebraicGeometry.NormalBundle

/-! # The canonical projection of the extended-Rees normal cone

The cone map factors through the closed immersion, independently of its
comparison with the relative spectrum of the conormal graded algebra.

## References

* Stacks Tags 062Z and 0630
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.AffineZariskiSite
namespace AlgebraicGeometry.Scheme.Hom

/-- The actual cone-to-X map factors through the closed immersion. -/
theorem purityNormalCone_kernel {Z X : Scheme.{u}} (i : Z ⟶ X) :
    i.ker ≤ (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase.ker := by
  have h := i.ker.normalConeToQuotientSpec.le_ker_comp
    (relativeGluingData i.ker.coequifibered_toQuotientAlgebra).toBase
  rw [i.ker.normalConeToQuotientSpec_toBase, i.ker.ker_quotientSpec_toBase] at h
  exact h

/-- The projection of the actual normal cone to Z, using the unique closed-immersion
factorization; its source is the extended-Rees quotient by t. -/
noncomputable def purityNormalProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : i.ker.normalCone ⟶ Z :=
  IsClosedImmersion.lift i
    (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase
    (purityNormalCone_kernel i)

/-- For a section `g` of `i`, the canonical factorization to `Z` is the normal-cone projection
formed using the retraction `g`. -/
theorem purityNormalProjection_eq {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (g : X ⟶ Z) (hs : i ≫ g = 𝟙 Z) :
    purityNormalProjection i = normalConeProj g i := by
  rw [normalConeProj, ← IsClosedImmersion.lift_fac i
    (relativeGluingData i.ker.coequifibered_toNormalConePresheaf).toBase
    (purityNormalCone_kernel i), Category.assoc, hs, Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Hom
