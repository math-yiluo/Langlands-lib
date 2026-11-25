/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCohomologicalDimensionDirectImageCoproducts
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound

/-!
# Coproducts and proper derived direct image

## References

* Stacks Project, Tags 0A3V, 095U and 0F11
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Proper direct image with finite commutative coefficients preserves every set-indexed
coproduct on the ordinary unbounded derived categories. Its restriction to the bounded-below
category agrees with the bounded-below derived direct image.
-/
theorem proper_rightDerivedLowerStar_preservesCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (r : V ⟶ T) [IsProper r]
    [IsLocallyNoetherian V] [CompactSpace V] [IsLocallyNoetherian T] [CompactSpace T] :
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) r)) ∧
    Nonempty
      (rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) r ⋙
          _root_.DerivedCategory.Plus.ι ≅
        _root_.DerivedCategory.Plus.ι ⋙ rightDerivedLowerStar (ModuleCat.{u + 1} A) r) := by
  obtain ⟨d, hd⟩ := exists_fibre_dimension_bound r
  refine ⟨?_, ⟨(lowerStar (ModuleCat.{u + 1} A) r).rightDerivedFunctorPlusCompatibility⟩⟩
  apply rightDerivedLowerStar_preservesCoproducts_of_finite_dimension A r (2 * d)
  intro M p hp
  let F := (sheafCompose V.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M
  have hF : Scheme.IsTorsionAbelianSheaf F := by
    apply (Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro W
    exact IsAddTorsion.module_of_finite A (M.obj.obj W)
  have hvan := isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    r d hd F hF (p : ℤ) (by exact_mod_cast hp)
  obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso A r (p : ℤ) M
  have hmod := hvan.of_iso e
  have hzero : IsZero (higherDirectImage A r (p : ℤ) M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map_injective
    exact hmod.eq_of_src _ _
  exact hzero.of_iso
    ((lowerStar (ModuleCat.{u + 1} A) r).homologyRightDerivedFunctorPlusObjSingleFunctorIso
      M p).symm

end AlgebraicGeometry.Etale
