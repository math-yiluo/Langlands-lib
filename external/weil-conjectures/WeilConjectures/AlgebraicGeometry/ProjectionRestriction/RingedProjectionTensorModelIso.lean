/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-!
# Normalized comparison with the derived tensor
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u + 1}}

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  HomologicalComplex₂.total MorphismProperty.Q'
  SheafOfModules.KFlatFixedTensor.representativeIso

private theorem publishedRepresentative (P Q : CochainComplex (Mod R) ℤ)
    (hp : resolving R P) (hq : resolving R Q) :
    SheafOfModules.cochainTensorRepresentativeArrow J R (⟨P, hp⟩, ⟨Q, hq⟩) =
      (SheafOfModules.KFlatFixedTensor.representativeIso R P Q hp.1 hq.1 hp.2 hq.2).hom := by
  unfold SheafOfModules.cochainTensorRepresentativeArrow
    SheafOfModules.KFlatFixedTensor.representativeIso
  simp only [id_eq, SheafOfModules.KFlatFixedTensor.TensorPresentation.representativeIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.prod_hom, Category.assoc]
  rfl

-- Compare the two normalized representative interfaces without unfolding their tensor data.
/-- A tensor model is naturally identified with the derived tensor, with
its specified representative comparison. -/
theorem ringedProjectionTensorModelIso (a : TensorModel R) :
    ∃ e : SheafOfModules.siteDerivedTensorIndependentCoefficients J R ≅ a.functor,
      ∀ (P Q : CochainComplex (Mod R) ℤ) (hp : resolving R P) (hq : resolving R Q),
        (SheafOfModules.KFlatFixedTensor.representativeIso R P Q hp.1 hq.1 hp.2 hq.2).hom ≫
          e.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
            a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) := by
  obtain ⟨r, hr, he, _⟩ :=
    SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u, u + 1, u + 2, 0, 0} J R
  obtain ⟨e, he, _⟩ := he a.functor a.representative
  refine ⟨e, ?_⟩
  intro P Q hp hq
  have h := congr_app he (⟨P, hp⟩, ⟨Q, hq⟩)
  change r.hom.app _ ≫ e.hom.app _ = _ at h
  rw [hr, publishedRepresentative P Q hp hq] at h
  exact h

end AlgebraicGeometry.Scheme.ProjectionRestriction
