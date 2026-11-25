/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ExactTensor.ProjectionExactTensorFirstShift
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ExactTensor.ProjectionExactTensorSecondShift

/-! Exact tensor functors on resolving representatives.

## References

* Stacks Project, Tags 06YU, 07A4 and 0FNH
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

namespace ExactTensor

/-- An exact tensor functor preserving coproducts and resolving complexes descends
with its representative normalization and both signed shift squares. -/
theorem exactTensorComparison_exists (L : Mod R ⥤ Mod S) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesColimitsOfSize.{0, 0} L]
    (a : TensorModel R) (b : TensorModel S) (sa : TensorShifts a) (sb : TensorShifts b)
    (mu : ∀ M N : Mod R, L.obj (((tensor R).obj M).obj N) ≅
      ((tensor S).obj (L.obj M)).obj (L.obj N))
    (hn : ∀ {M M' N N' : Mod R} (f : M ⟶ M') (g : N ⟶ N'),
      L.map (((tensor R).map f).app N ≫ ((tensor R).obj M').map g) ≫
        (mu M' N').hom =
      (mu M N).hom ≫ (((tensor S).map (L.map f)).app (L.obj N) ≫
        ((tensor S).obj (L.obj M')).map (L.map g)))
    (hp : ∀ P, resolving R P → resolving S ((L.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ t : TensorComparison L (exactTensorModel L) a b mu,
      TensorComparisonShifts t (sa := sa) (sb := sb) (sd := inferInstance) := by
  obtain ⟨t⟩ := exactTensorComparison_nonempty L a b mu hn hp
  let := sa
  let := sb
  exact ⟨t, ⟨exactTensorComparison_shiftFirst L a b mu hn t,
    exactTensorComparison_shiftSecond L a b mu hn t⟩⟩

end ExactTensor
end AlgebraicGeometry.Scheme.ProjectionRestriction
