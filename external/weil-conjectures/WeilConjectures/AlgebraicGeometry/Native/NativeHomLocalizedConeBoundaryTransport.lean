/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeHomLocalizedConeBoundaryModel
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Transport of the native Hom cone boundary

## References

* Stacks Project, Tags 08J9 and 08JC
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

private theorem signedSource_coefficient_naturality
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [MonoidalCategory D] [MonoidalClosed D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]
    {M N : D} (g : M ⟶ N) (n : ℤ) (X : Dᵒᵖ) :
    (MonoidalClosed.internalHom.flip.map g).app (X⟦n⟧) ≫
        siteHomSignedSourceComponent N n X =
      siteHomSignedSourceComponent M n X ≫
        ((MonoidalClosed.internalHom.flip.map g).app X)⟦n⟧' := by
  change (ihom (X.unop⟦-n⟧)).map g ≫ _ = _ ≫ ((ihom X.unop).map g)⟦n⟧'
  have h := (siteHomOppositeSourceShift X.unop n).hom.naturality g
  simpa only [siteHomSignedSourceComponent, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Units.smul_def, Functor.comp_map] using
    congrArg (fun z ↦ (n * (n + 1) / 2).negOnePow • z) h

/-- An isomorphism `e` from the localization of a K-injective complex `I` to `M` induces an
isomorphism between the internal-Hom cone triangles of `f` with coefficients in `I` and in `M`. -/
theorem nativeHom_localized_cone_boundary_transport
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G)
    (I : CochainComplex C ℤ) [I.IsKInjective]
    (M : DerivedCategory C) (e : DerivedCategory.Q.obj I ≅ M) :
    let M₀ := DerivedCategory.Q.obj I
    let H₀ := MonoidalClosed.internalHom.flip.obj M₀
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Nonempty (Triangle.mk (H₀.map T.mor₁) (H₀.map T.mor₂)
      (H₀.map T.mor₃ ≫ siteHomSignedSourceComponent M₀ 1 T.obj₁) ≅
      Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
        (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁)) := by
  let M₀ := DerivedCategory.Q.obj I
  let H₀ := MonoidalClosed.internalHom.flip.obj M₀
  let H := MonoidalClosed.internalHom.flip.obj M
  let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
    (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
  let α : H₀ ≅ H := MonoidalClosed.internalHom.flip.mapIso e
  have hs (X : (DerivedCategory C)ᵒᵖ) :
      α.hom.app (X⟦(1 : ℤ)⟧) ≫ siteHomSignedSourceComponent M 1 X =
        siteHomSignedSourceComponent M₀ 1 X ≫ (α.hom.app X)⟦(1 : ℤ)⟧' := by
    simpa only [α, Functor.mapIso_hom] using
      signedSource_coefficient_naturality e.hom 1 X
  refine ⟨Triangle.isoMk _ _ (α.app T.obj₁) (α.app T.obj₂) (α.app T.obj₃)
    (α.hom.naturality T.mor₁) (α.hom.naturality T.mor₂) ?_⟩
  change (H₀.map T.mor₃ ≫ siteHomSignedSourceComponent M₀ 1 T.obj₁) ≫
      (α.hom.app T.obj₁)⟦(1 : ℤ)⟧' =
    α.hom.app T.obj₃ ≫ H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁
  rw [Category.assoc, ← hs, ← Category.assoc, α.hom.naturality, Category.assoc]

end AlgebraicGeometry.ProEtale
