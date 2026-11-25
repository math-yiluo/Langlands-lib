/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.AlgebraicGeometry.FiniteSheafHomAffineAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Right adjoint to derived restriction along the direct-image algebra

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BV1 and 0AX3
(blueprint: lem-sc-finite-restriction-derived-right-adjoint). -/

@[expose] public section

universe u wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Supply the auxiliary adjunction required by finite derived duality. This asserts
only an adjoint to derived restriction of algebra scalars; it makes no assertion about
f's right adjoint, its degree-zero representative, or its counit.

Source: Stacks Project, Duality for Schemes, Tags 0BV0, 0BV1 and 0AX3
(blueprint: lem-sc-finite-restriction-derived-right-adjoint).

Proof:
1. Apply `exists_affine_derivedSheafHom_adjunction` to f. This supplies the derived
   sheaf-Hom functor H, the left functor T, the adjunction T |- H, and a natural
   isomorphism Q ⋙ T ≅ restrictScalars.mapHomologicalComplex ⋙ Q.
2. Restriction of scalars is exact: kernels and cokernels retain their underlying
   abelian sheaves, with the restricted action. The finite-limit and finite-colimit
   clauses of `derivedRHomAlgebraModule` apply to the algebra sheaf f_* O_X.
   Consequently its termwise functor descends to mapDerivedCategory.
3. Compose the factorization isomorphism of mapDerivedCategory with the inverse
   of T's factorization. Full faithfulness of precomposition by the localization Q
   descends this to T ≅ restrictScalars.mapDerivedCategory. The exact-functor
   comparison `rightDerivedFunctorIsoMapDerivedCategory` identifies the latter
   with restrictScalars.rightDerivedFunctor.
4. Transport T |- H along this natural isomorphism (`Adjunction.ofNatIsoLeft`).
   Its right adjoint H is the required witness. This does not require a nonempty
   scheme, nonzero algebra, finite rank, or Noetherianity. -/
theorem finiteRestriction_derived_rightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))] :
    ∃ (H : DerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))),
      Nonempty ((SheafOfModules.restrictScalars
        (R := moduleRings Y.toRingedSpace)
        (R' := moduleRings (directImageAlgebraSpace f))
        ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) := by
  classical
  let B : Y.CommAlgebraSheaf := Under.mk
    (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf from ⟨f.c⟩)
  let F := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    change HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))
    infer_instance
  have : PreservesFiniteLimits F := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits F := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  obtain ⟨_, _, _, _, _, H, _, T, t, adj, _⟩ := exists_affine_derivedSheafHom_adjunction f
  let : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) T := ⟨t⟩
  let e : T ≅ F.mapDerivedCategory := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    T F.mapDerivedCategory (Iso.refl _)
  exact ⟨H, ⟨adj.ofNatIsoLeft (e ≪≫ F.rightDerivedFunctorIsoMapDerivedCategory.symm)⟩⟩

end AlgebraicGeometry
