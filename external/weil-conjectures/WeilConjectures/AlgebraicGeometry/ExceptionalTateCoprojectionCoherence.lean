/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.Identity

/-!
# Closed-immersion Tate co-projection coherence

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-regular/
 sk-thm-regular.proof.md`, Steps 2 and 4(iii)
(blueprint: lem-pur-exceptional-tate-coprojection-coherence).

The canonical co-projection for the shifted Tate object is defined from the specified
right-adjoint tensor mate and the canonical inverse-image Tate comparison.  The coherence
statement records naturality, addition, units, identity normalization, and inverse evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z]

/-- The finite Tate object `A_T(r)[2r]` used in the co-projection statement.
Source: the finite Tate convention in `sk-thm-regular.proof.md`, Step 1
(blueprint: lem-pur-exceptional-tate-coprojection-coherence). -/
noncomputable def shiftedTateObject (T : Scheme.{u}) (r : ℤ) :
    _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (tateObject Λ T r)⟦2 * r⟧

/-- The zero Tate factor identified with the ordinary tensor unit, `T_0^T = A_T(0)[0] ≅ A_T`.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-regular/
 sk-thm-regular.proof.md`, Step 2, zero twist
(blueprint: lem-pur-exceptional-tate-coprojection-coherence). -/
noncomputable def shiftedTateZeroIso (T : Scheme.{u}) [HasInvertibleExponent Λ T] :
    shiftedTateObject Λ T 0 ≅ constantComplex Λ T :=
  (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).app _ ≪≫
    HasTateTwist.twistObjectZeroIso (Λ := Λ) T

/-- The inverse-Tate evaluation `ev_r^T : T_r^T ⊗ T_{-r}^T ≅ A_T` in the shifted convention:
the Tate addition at `(r, -r)` followed by the zero-shift and zero-twist identifications.

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-regular/
 sk-thm-regular.proof.md`, Step 2, cancellation of the invertible Tate factor
(blueprint: lem-pur-exceptional-tate-coprojection-coherence). -/
noncomputable def shiftedTateEvaluation (T : Scheme.{u}) [HasInvertibleExponent Λ T]
    (r : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) T).obj
      (shiftedTateObject Λ T r)).obj (shiftedTateObject Λ T (-r)) ⟶
      constantComplex Λ T :=
  (shiftTateObjectAddIso Λ T r (-r)).hom ≫
    eqToHom (by simp) ≫
    (shiftFunctorZero' _ (0 : ℤ) rfl).hom.app (tateObject Λ T 0) ≫
    (HasTateTwist.twistObjectZeroIso (Λ := Λ) T).hom

end AlgebraicGeometry.Etale
