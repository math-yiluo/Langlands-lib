/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Good representatives of integral constructible objects

Every intrinsic integral constructible object is isomorphic to the localization of a K-flat
complex with flat terms.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralScalarExtension integralOrdinaryScalar

/-- Every intrinsic integral constructible object has a good representative. -/
theorem sfIntegralConstructible_goodRepresentative (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : AlgebraicGeometry.Scheme.{u})
    (K : sfIntegralConstructibleCategory l E Y) :
    ∃ (V : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (hV : sfIntegralConstructible l E Y (DerivedCategory.Q.obj V.obj)),
      Nonempty ((⟨DerivedCategory.Q.obj V.obj, hV⟩ : sfIntegralConstructibleCategory l E Y) ≅
        K) := by
  let Q := DerivedCategory.Q (C := integralTowerModules.{u, u} l E Y)
  let T := Q.objPreimage K.obj
  let e := Q.objObjPreimageIso K.obj
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
  let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  obtain ⟨P, f, hflat, hterms, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u+1, u+1, u}
      (C := Y.ProEt) (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) T
  have : QuasiIso f := hf
  let e' : Q.obj P ≅ K.obj := asIso (Q.map f) ≪≫ e
  have hP : sfIntegralConstructible l E Y (Q.obj P) :=
    (sfIntegralConstructible l E Y).prop_of_iso e'.symm K.property
  have hg : integralOperationsGoodComplex.{u, u} l E Y P :=
    ⟨hflat, fun i ↦ (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u+1, u, u+1}
        (completedIntegralCommRingSheafUnrestricted.{u, u} l E Y) (P.X i)).symm (hterms i)⟩
  exact ⟨⟨P, hg⟩, hP, ⟨
    { hom := ⟨e'.hom⟩
      inv := ⟨e'.inv⟩
      hom_inv_id := by ext; exact e'.hom_inv_id
      inv_hom_id := by ext; exact e'.inv_hom_id }⟩⟩

end WeilConjectures
