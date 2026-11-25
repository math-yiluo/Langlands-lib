/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTensorTransport.ProEtaleCoefficientPullback
public import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement

/-! # The ordinary coefficient restriction tensor square

Source: Stacks, Modules on Sites, Tag 03EL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  AlgebraicGeometry.Scheme.proEtaleRingModuleDirectImage
  SheafOfModules.pushforward SheafOfModules.restrictScalars
  PresheafOfModules.pushforward PresheafOfModules.restrictScalars
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalarsObj
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorChain

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

private theorem tensor_pair_map {M M' N N' : proEtaleRingModules Y R}
    (v : M ⟶ M') (w : N ⟶ N') (V : Y.ProEtᵒᵖ)
    (m : M.val.obj V) (n : N.val.obj V) :
    ((SheafOfModules.monoidalCategory R).tensorHom v w).val.app V
        (proEtaleTensorPair Y R M N V m n) =
      proEtaleTensorPair Y R M' N' V (v.val.app V m) (w.val.app V n) := by
  exact SheafOfModules.ScalarHomOrdinary.pure_map R v w V m n

private theorem ordinaryPullback_inv_unit (M : proEtaleRingModules Y R)
    (V : Y.ProEtᵒᵖ) (m : M.val.obj V) :
    ((ordinaryPullback f R S c).inv.app M).val.app
        ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _)).unit.app M).val.app V m) =
      ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app
        V m := by
  have hm := unit_mateEquiv
    (proEtaleRingModuleAdjunction f R S c)
    (proEtaleRingModuleAdjunction f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp))) M
  have hmate := restrictionPullback_mate f R R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
    (𝟙 R) c.hom (Iso.refl _) c (by simp)
  rw [hmate] at hm
  have h := congrArg (fun v ↦ v.val.app V m) hm
  have hd := (Classical.choose_spec
    (proEtaleRingRestrictionDirectImage_existsUnique f R R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S
      (𝟙 R) c.hom (Iso.refl _) c (by simp))).1
    ((proEtaleRingModulePullback f R S c).obj M) V
    (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m)
  dsimp only [ordinaryPullback, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerRight_inv, whiskerRight_app, leftUnitor_inv_app, Iso.refl_inv, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, asIso_hom]
  exact h.symm.trans hd

private theorem ordinary_tensor_pure (M N : proEtaleRingModules Y R)
    (V : Y.ProEtᵒᵖ) (m : M.val.obj V) (n : N.val.obj V) :
    (proEtaleOrdinaryTensorPullback f R S c M N).hom.val.app
        ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R S c).unit.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N)).val.app V
            (proEtaleTensorPair Y R M N V m n)) =
      proEtaleTensorPair X S ((proEtaleRingModulePullback f R S c).obj M)
        ((proEtaleRingModulePullback f R S c).obj N) ((proEtaleBaseChange f).op.obj V)
        (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m)
        (((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app V n) := by
  exact (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).2 M N V.unop m n

attribute [local irreducible] ordinaryPullback proEtaleOrdinaryTensorPullback
  proEtaleRingModulePullback

private theorem ordinary_inverse_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (ordinaryPullback f R S c).inv.app
        (((proEtaleOrdinaryTensor Y R).obj M).obj N) ≫
        (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).hom ≫
        o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) =
      (proEtaleOrdinaryTensorPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _) M N).hom ≫
        (SheafOfModules.monoidalCategory
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
          ((ordinaryPullback f R S c).inv.app M)
          ((ordinaryPullback f R S c).inv.app N) := by
  apply ((proEtaleRingModuleAdjunction f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    (Iso.refl _)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext R M N _
  intro V m n
  have hc := ordinary_tensor_pure f R S c M N V m n
  have hi := ordinary_tensor_pure f R
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
    (Iso.refl _) M N V m n
  change (o.monoidal.toMonoidal.toOplaxMonoidal.δ _ _).val.app _
      ((proEtaleOrdinaryTensorPullback f R S c M N).hom.val.app _
        (((ordinaryPullback f R S c).inv.app _).val.app _
          (((proEtaleRingModuleAdjunction f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _)).unit.app _).val.app V
            (proEtaleTensorPair Y R M N V m n)))) =
    ((SheafOfModules.monoidalCategory
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
        ((ordinaryPullback f R S c).inv.app M)
        ((ordinaryPullback f R S c).inv.app N)).val.app _
      ((proEtaleOrdinaryTensorPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _) M N).hom.val.app _
          (((proEtaleRingModuleAdjunction f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _)).unit.app _).val.app V
            (proEtaleTensorPair Y R M N V m n)))
  erw [ordinaryPullback_inv_unit f R S c, hc, hi]
  rw [tensor_pair_map,
    ordinaryPullback_inv_unit f R S c, ordinaryPullback_inv_unit f R S c]
  exact o.pure_hom _ _ _ _ _

private theorem invert_square {A : Type*} [Category* A]
    {a b d e z : A} (mu : a ≅ b) (beta : a ≅ d) (nu : d ≅ e)
    (pair : z ≅ e) (delta : b ⟶ z)
    (h : beta.inv ≫ mu.hom ≫ delta = nu.hom ≫ pair.inv) :
    mu.inv ≫ beta.hom = delta ≫ pair.hom ≫ nu.inv := by
  apply (cancel_epi mu.hom).1
  apply (cancel_epi beta.inv).1
  have hh := congrArg (fun v ↦ v ≫ pair.hom ≫ nu.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Iso.inv_hom_id, Category.comp_id] using hh.symm

/-- Coefficient restriction commutes with the canonical ordinary tensor pullback.

Source: Stacks, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback.
(blueprint: lem-pbc-coefficient-restriction-ordinary-tensor-square)

Proof: apply the module pullback adjunction to the inverse-oriented square.
The mate-unit identity and the sectionwise identity direct-image comparison show
that inverse coefficient transport preserves the pullback unit. Both geometric
tensor maps carry unit pure tensors to the tensor of the two unit sections.
The supplied restriction tensorator fixes pure sections, and tensor functoriality
identifies the other route. Sheafified pure-tensor extensionality proves equality.
Finally cancel the ordinary tensor and coefficient isomorphisms to reverse the square. -/
theorem ordinary_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).inv ≫
        (ordinaryPullback f R S c).hom.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) ≫
        (SheafOfModules.monoidalCategory
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).tensorHom
          ((ordinaryPullback f R S c).hom.app M)
          ((ordinaryPullback f R S c).hom.app N) ≫
        (proEtaleOrdinaryTensorPullback f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _) M N).inv := by
  let := SheafOfModules.monoidalCategory
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  exact invert_square
    ((pbcRestrict c.hom).mapIso (proEtaleOrdinaryTensorPullback f R S c M N))
    ((ordinaryPullback f R S c).app _)
    (proEtaleOrdinaryTensorPullback f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) M N)
    (MonoidalCategory.tensorIso ((ordinaryPullback f R S c).app M)
      ((ordinaryPullback f R S c).app N)) _
    (ordinary_inverse_square f R S c o M N)

private theorem complex_component (P : CochainComplex (proEtaleRingModules Y R) ℤ)
    (n : ℤ) :
    ((complexPullback f R S c).hom.app P).f n =
      (ordinaryPullback f R S c).hom.app (P.X n) := by
  simp only [complexPullback, Functor.mapHomologicalComplexCompIso_hom_app_f]

private theorem ordinary_bifunctor_square
    (o : SheafOfModules.RingIsoTensorTransport
      (J := ProEt.topology X)
      (R := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (S := S) c)
    (M N : proEtaleRingModules Y R) :
    (pbcRestrict c.hom).map (proEtaleOrdinaryTensorPullback f R S c M N).inv ≫
        (ordinaryPullback f R S c).hom.app
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) =
      o.monoidal.toMonoidal.toOplaxMonoidal.δ
          ((proEtaleRingModulePullback f R S c).obj M)
          ((proEtaleRingModulePullback f R S c).obj N) ≫
        ((proEtaleOrdinaryTensor X
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map
            ((ordinaryPullback f R S c).hom.app M)).app
              ((pbcRestrict c.hom).obj ((proEtaleRingModulePullback f R S c).obj N)) ≫
        ((proEtaleOrdinaryTensor X
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).obj
            ((proEtaleRingModulePullback f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _)).obj M)).map ((ordinaryPullback f R S c).hom.app N) ≫
        (proEtaleOrdinaryTensorPullback f R
          ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
          (Iso.refl _) M N).inv := by
  simpa only [proEtaleOrdinaryTensor, MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Category.assoc] using ordinary_square f R S c o M N

end AlgebraicGeometry.Scheme.CoefficientTensorChain
