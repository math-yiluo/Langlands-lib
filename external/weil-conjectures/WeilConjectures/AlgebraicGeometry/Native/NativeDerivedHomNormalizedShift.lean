/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.CategoryTheory.SixFunctors.HomShiftEvaluationNormalization
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomMateEvaluation

/-! # Evaluation-normalized native derived internal Hom

## References

* Stacks Project, Tags 08JC and 08J9
-/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The native signed exact shift also satisfies the tensor-Hom evaluation identity. -/
theorem derivedHom_normalizedShift_exists
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    (M : _root_.DerivedCategory C) :
    ∃ s : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ,
      homShiftEvaluationNormalization M s ∧
        (letI := s; (MonoidalClosed.internalHom.flip.obj M).IsTriangulated) := by
  obtain ⟨s, ht, hs⟩ := ProEtale.nativeDerivedHom_signed_exact.{u, d} (C := C) M
  refine ⟨s, ?_, ht⟩
  exact etaleHom_signedMateEvaluation M s hs

end AlgebraicGeometry.Etale
