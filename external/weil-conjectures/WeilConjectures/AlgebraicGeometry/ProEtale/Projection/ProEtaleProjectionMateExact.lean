/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionMateData
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Exactness and the coefficient-unit normalization of the pro-etale mate

## References

* Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

/-- The two coefficient functors of the actual pro-etale projection mate are exact,
and its natural transformation respects shifts and is invertible at the ring. -/
theorem proEtaleProjectionMateExact :
    ∃ (sF : ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).CommShift ℤ)
      (sG : (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).CommShift ℤ),
      ((Functor.curryObj a.tensor).obj
        ((proEtaleRingDerivedDirectImage f R S c).obj E)).IsTriangulated ∧
      (proEtaleRingDerivedPullback f R S c ⋙
        (Functor.curryObj b.tensor).obj E ⋙
          proEtaleRingDerivedDirectImage f R S c).IsTriangulated ∧
      ∃ τ : (Functor.curryObj a.tensor).obj
          ((proEtaleRingDerivedDirectImage f R S c).obj E) ⟶
        proEtaleRingDerivedPullback f R S c ⋙
          (Functor.curryObj b.tensor).obj E ⋙ proEtaleRingDerivedDirectImage f R S c,
        (∀ P, τ.app P = proEtaleProjectionFormulaMate f R S c a b E P) ∧
        NatTrans.CommShift τ ℤ ∧
        IsIso (τ.app ((DerivedCategory.singleFunctor (proEtaleRingModules Y R) 0).obj
          (SheafOfModules.unit ((sheafCompose (ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))) :=
  proEtaleProjectionMateData.{u} f R S c a b E
end AlgebraicGeometry.Scheme
