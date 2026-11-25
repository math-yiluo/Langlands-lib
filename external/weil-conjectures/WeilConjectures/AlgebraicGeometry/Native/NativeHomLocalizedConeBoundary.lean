/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSignedShiftLaws
import WeilConjectures.AlgebraicGeometry.Native.NativeHomLocalizedConeBoundaryTransport
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # The signed native Hom boundary on localized cone triangles

## References

* Stacks Project, Tags 08J9 and 08JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

/-- On a localized ordinary cone triangle the specified signed boundary makes
contravariant native Hom into a distinguished triangle. -/
theorem nativeHom_localized_cone_boundary
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G) (M : DerivedCategory C) :
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
      (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁) ∈
        distTriang (DerivedCategory C) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let M₀ := DerivedCategory.Q.obj I
  let H₀ := MonoidalClosed.internalHom.flip.obj M₀
  let H := MonoidalClosed.internalHom.flip.obj M
  let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
    (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
  have hmodel :
      Triangle.mk (H₀.map T.mor₁) (H₀.map T.mor₂)
          (H₀.map T.mor₃ ≫ siteHomSignedSourceComponent M₀ 1 T.obj₁) ∈
        distTriang (DerivedCategory C) :=
    nativeHom_localized_cone_boundary_model f I
  obtain ⟨eT⟩ := nativeHom_localized_cone_boundary_transport f I M e.symm
  exact Pretriangulated.isomorphic_distinguished _ hmodel _ eT.symm

end AlgebraicGeometry.ProEtale
