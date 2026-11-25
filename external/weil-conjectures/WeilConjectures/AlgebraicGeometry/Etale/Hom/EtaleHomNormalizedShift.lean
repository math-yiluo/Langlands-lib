/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomNormalizedShift

/-! # Evaluation-normalized exact shift for one étale Hom functor -/

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory

/-- A single coefficient Hom functor admits the evaluation-normalized exact shift.
Source: Stacks Project, Tags 08JC and 08J9, signed Hom reindexing and the
termwise split sequence argument.

Proof: use the existing native signed exact Hom theorem. Its degree-n component
is the quadratic sign times the explicit right-adjoint source-shift mate.
The right-adjoint uniqueness counit identity identifies the raw mate, followed by
tensor-shift cancellation and evaluation, with evaluation at the shifted source.
Multiply the signed component by the same sign; integer units square to one.
Specializing this generic calculation to the category of etale sheaves gives the
normalization for the same shift that the native theorem proves triangulated.
The mate identity holds for every integer, including zero and negative integers,
and sign cancellation also holds in characteristic two.
(blueprint: lem-coef-etale-hom-normalized-single-shift) -/
theorem etaleHom_normalizedShift_exists
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ∃ s : ((derivedHom C X).flip.obj M).CommShift ℤ,
      EtaleHomShiftNormalization C X M s ∧
        (letI := s; ((derivedHom C X).flip.obj M).IsTriangulated) := by
  exact derivedHom_normalizedShift_exists.{u, u + 2}
    (C := Sheaf X.smallEtaleTopology C) M

end AlgebraicGeometry.Etale
