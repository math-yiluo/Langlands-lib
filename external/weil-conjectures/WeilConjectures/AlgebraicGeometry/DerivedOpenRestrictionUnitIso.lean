/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import WeilConjectures.Algebra.Homology.OpenExtensionRestrictionIso
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Restriction inverts the derived open-adjunction unit

Source: Stacks Project, Cohomology, Tags 08BS and 08FE.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

noncomputable section

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Exact-open restriction makes the unit of its right adjunction invertible.
Source: Stacks Project, Cohomology, Tags 08BS and 08FE.
(blueprint: lem-pc-scheme-derived-open-unit-restriction-iso).
Proof: Transport the concrete extension-by-zero adjunction across the equivalence
between modules on the over-site and modules on the open subscheme. This gives
an exact left adjoint G to exact-open restriction F. The underived composite
G;F is the identity, using the existing extension-by-zero restriction isomorphism
and the equivalence counit. Derive both exact functors and localize the termwise
adjunction. The derived composition and identity comparisons give G_D;F_D≅id,
so G_D is fully faithful. In the adjoint triple G_D⊣F_D⊣R, full faithfulness
of G_D implies full faithfulness of R. Its adjunction counit is therefore
invertible, and the triangle identity makes F_D of the unit its inverse.
This applies to any supplied right adjunction, including empty opens, without
adding a derived-category instance for the intermediate over-site category. -/
theorem schemeDerivedOpen_unit_isIso (X : Scheme.{u}) (U : X.Opens)
    (adj : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
    (K : schemeDerivedCategory X) :
    IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map (adj.unit.app K)) := by
  classical
  let A := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let E := Scheme.Modules.overEquiv U
  let F₀ := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let G₀ := SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X.toRingedSpace) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X.toRingedSpace).obj)
  obtain ⟨_, _, hlim, hcolim, ⟨adjG₀⟩⟩ :=
    open_restriction_adjunction_exact X.toRingedSpace U
  let : PreservesFiniteLimits G₀ := hlim
  let : PreservesFiniteColimits G₀ := hcolim
  let G : A ⥤ B := E.inverse ⋙ G₀
  let F : B ⥤ A := schemeOpenRestriction X U
  let : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  let adjG : G ⊣ F := E.symm.toAdjunction.comp adjG₀
  let : G.Additive := adjG.left_adjoint_additive
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let adjD : G.mapDerivedCategory ⊣ F.mapDerivedCategory :=
    (adjG.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
      G.mapDerivedCategory F.mapDerivedCategory
  obtain ⟨e₀⟩ := nonempty_openExtensionRestrictionIso X.toRingedSpace U
  let e : G ⋙ F ≅ 𝟭 A :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft E.inverse
        ((Functor.associator G₀ F₀ E.functor).symm ≪≫
          Functor.isoWhiskerRight e₀ E.functor ≪≫ Functor.leftUnitor E.functor) ≪≫
      E.counitIso
  let : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits _ _
  let eD : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
    (Functor.mapDerivedCategoryCompIso G F) ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A
  let ff := adjD.fullyFaithfulLOfCompIsoId eD
  let ffR := (Adjunction.Triple.fullyFaithfulEquiv ⟨adjD, adj⟩) ff
  let : (schemeDerivedDirectImage U.ι).Full := ffR.full
  let : (schemeDerivedDirectImage U.ι).Faithful := ffR.faithful
  exact inferInstance

end

end AlgebraicGeometry
