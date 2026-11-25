/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientRealizationDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations

/-! # Proper direct image preserves coproducts of classical complexes

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-ctf-finite-proper-localizing.proof.md, Étale statements and Transfer
(blueprint: lem-sfb-finite-proper-classical-coproducts).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

private theorem etale_cd (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (e : ℕ)
    (he : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (e : WithBot ℕ∞)) :
    ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ), 2 * e < p →
      IsZero (((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M) := by
  intro M p hp
  let F := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M
  have hF : Scheme.IsTorsionAbelianSheaf F := by
    apply (Scheme.isTorsionAbelianSheaf_characterizations F).1.mpr
    apply Sheaf.IsTorsion.of_forall_isAddTorsion
    intro W
    exact IsAddTorsion.module_of_finite A (M.obj.obj W)
  have hvan := Etale.isZero_higherDirectImage_of_isProper_of_fiber_dimension_le
    f e he F hF (p : ℤ) (by exact_mod_cast hp)
  obtain ⟨i⟩ := Etale.nonempty_higherDirectImage_forget_iso A f (p : ℤ) M
  have hmod := hvan.of_iso i
  have hz : IsZero (Etale.higherDirectImage A f (p : ℤ) M) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).map_injective
    exact hmod.eq_of_src _ _
  exact hz.of_iso
    ((Etale.lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
      M p).symm

end AlgebraicGeometry.ProEtale
