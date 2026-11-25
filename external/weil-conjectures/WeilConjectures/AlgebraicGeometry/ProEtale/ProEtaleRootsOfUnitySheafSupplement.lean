/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleStructureSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf

/-! # Roots of unity on the small pro-etale site

The power map, kernel, constant-ring module and transition maps use the original
sectionwise global-sections rings. No invertibility hypothesis on the exponent is imposed.

## References

* Stacks Project, Section 59.28, Tag 03PK
* Stacks Project, Tag 03P4
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- For divisible exponents both sheaves are killed by the larger exponent. -/
theorem proEtaleRootsOfUnity_nsmul_of_dvd (S : Scheme.{u}) (N N' : ℕ) (h : N ∣ N')
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) : N' • x = 0 := by
  obtain ⟨k, rfl⟩ := h
  simp [mul_comm N k, mul_nsmul, proEtaleRootsOfUnity_nsmul]

/-- For a prime `ℓ`, the transition between consecutive powers is `x ↦ x^ℓ`. -/
theorem proEtaleRootsOfUnityTransition_prime (S : Scheme.{u}) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (r : ℕ) (U : S.ProEtᵒᵖ)
    (x : (proEtaleRootsOfUnitySheaf S (ℓ ^ (r + 2))).obj.obj U) :
    (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 1))).hom.app U
      ((proEtaleRootsOfUnityTransition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
        (pow_pos hℓ.pos _) (pow_pos hℓ.pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (r + 1)))).hom.app U x) =
      ℓ • (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 2))).hom.app U x := by
  have hdiv : ℓ ^ (r + 2) / ℓ ^ (r + 1) = ℓ := by
    rw [show r + 2 = (r + 1) + 1 by omega, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hℓ.pos _)]
  have hh := kernel.lift_ι (proEtaleUnitsPower S (ℓ ^ (r + 1)))
    (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 2)) ≫
      ((ℓ ^ (r + 2) / ℓ ^ (r + 1)) • 𝟙 (proEtaleUnitsSheaf S)))
    (proEtaleRootsOfUnityTransition_condition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
      (pow_pos hℓ.pos _) (pow_pos hℓ.pos _)
      (pow_dvd_pow ℓ (Nat.le_succ (r + 1))))
  have hx := congrArg (fun f ↦ f.hom.app U x) hh
  change (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 1))).hom.app U
      ((proEtaleRootsOfUnityTransition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
        (pow_pos hℓ.pos _) (pow_pos hℓ.pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (r + 1)))).hom.app U x) =
      (ℓ ^ (r + 2) / ℓ ^ (r + 1)) •
        (proEtaleRootsOfUnityInclusion S (ℓ ^ (r + 2))).hom.app U x at hx
  rw [hdiv] at hx
  exact hx

/-- The inverse system indexed by `r ≥ 1`; the natural-number index `r` denotes `r+1`.
Each successor transition is the specified power map; arbitrary transitions are composites. -/
noncomputable def proEtaleRootsOfUnityTower (S : Scheme.{u}) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ℕᵒᵖ ⥤ Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun r ↦ proEtaleRootsOfUnitySheaf S (ℓ ^ (r + 1))) (fun r ↦
    proEtaleRootsOfUnityTransition S (ℓ ^ (r + 1)) (ℓ ^ (r + 2))
      (pow_pos hℓ.pos _) (pow_pos hℓ.pos _) (pow_dvd_pow ℓ (Nat.le_succ (r + 1))))

end AlgebraicGeometry.Scheme
