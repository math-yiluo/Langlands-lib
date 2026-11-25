/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorEpimorphic
import all WeilConjectures.AlgebraicGeometry.ProEtaleMilnorSequence
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.AlgebraicGeometry.MilnorTower
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.AlgebraicGeometry.AffineScheme
import all Mathlib.CategoryTheory.Sites.Sheaf
import all WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import all WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import all WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import all WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.RingTheory.ProEtale.WContractible
import all Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all Mathlib.RingTheory.RingHom.FaithfullyFlat
import all WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.RoosCohomologySequence
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyMaps
import all Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import all WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.AlgebraicGeometry.RoosCohomologyNaturality
import all Mathlib.Algebra.Homology.SingleHomology
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSurjectiveTowerDerivedLimitSupplement
import all Mathlib.Algebra.Category.ModuleCat.Products
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootTransitions
import WeilConjectures.CategoryTheory.Finite.FiniteTowerLimitOrthogonality

/-! # Proved helpers for completed diagonal endpoints

Source: the diagonal tower limit proof, paragraphs (1) and (3).
(blueprint: lem-sfb-diagonal-root-limit-linear).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b v w g
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalEndpointsProof

private theorem towerDifference_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (H : ℕᵒᵖ ⥤ DiagonalMod l T)
    (ht : ∀ n : ℕ, Epi (H.map (homOfLE (Nat.le_succ n)).op)) :
    Epi (towerTransitionEndomorphism (K := fun n : ℕ ↦ H.obj (op n))
      (fun n : ℕ ↦ H.map (homOfLE (Nat.le_succ n)).op)) := by
  obtain ⟨e, _, _, hi, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology T) (ULift.{u + 1} ℤ_[l])).1
  let E := e.inverse
  have : E.Additive := hi
  have h (n : ℕ) : Epi ((H ⋙ E).map (homOfLE (Nat.le_succ n)).op) := by
    have := ht n
    exact E.map_epi _
  have : Epi (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ E.obj (H.obj (op n)))
      (fun n : ℕ ↦ E.map (H.map (homOfLE (Nat.le_succ n)).op))) :=
    AlgebraicGeometry.ProEtale.sheaf_tower_epi.{0, u} T _ (H ⋙ E) h
  apply E.epi_of_epi_map
  apply (epi_comp_iff_of_isIso _ (piComparison E (fun n : ℕ ↦ H.obj (op n)))).mp
  rw [AlgebraicGeometry.ProEtale.map_transition]
  exact inferInstance

private theorem towerProducts_exact (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    HasExactLimitsOfShape (Discrete ℕ) (DiagonalMod l T) := by
  obtain ⟨e, _, _, _, _⟩ :=
    (constant_ring_module_sheaves (Scheme.ProEt.topology T) (ULift.{u + 1} ℤ_[l])).1
  have : HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1}
      ((constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1} ℤ_[l])))) :=
    Scheme.ProEt.products_exact.{u, 0, 0} T _ ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e

private theorem derivedUnit_isIso
    {A : Type a} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasExactLimitsOfShape (Discrete ℕ) A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (ht : ∀ p : ℤ, Epi (towerTransitionEndomorphism
      (K := fun n : ℕ ↦ (I.X p).obj (op n))
      (fun n : ℕ ↦ (I.X p).map (homOfLE (Nat.le_succ n)).op))) :
    IsIso (L.η.app I) := by
  let c : Cone I.asFunctor :=
    { pt := ExactProductsRoos.ordinary.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (.up ℤ)).app I
             naturality := by
               intro n m f
               ext p : 1
               change 𝟙 _ ≫ limit.π (I.X p) m =
                 limit.π (I.X p) n ≫ (I.X p).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro p
    exact limit.isLimit (I.X p)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  let i := ExactProductsRoos.inclusion.app I
  let t := ExactProductsRoos.difference.app I
  obtain ⟨hz, ⟨hk⟩⟩ := AlgebraicGeometry.ProEtale.tower_kernel I.asFunctor c hc P
    (limit.isLimit _) i t (fun n ↦ Pi.lift_comp_π _ n)
    (fun n ↦ (towerTransitionEndomorphism_eq_iff _ _).1 rfl n)
  have hte : Epi t := by
    apply HomologicalComplex.epi_of_epi_f
    intro p
    let ev := HomologicalComplex.eval A (.up ℤ) p
    have : Epi (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ev.obj (K n))
        (fun n : ℕ ↦ ev.map (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))) := ht p
    change Epi (ev.map t)
    apply (epi_comp_iff_of_isIso _ (piComparison ev K)).mp
    change Epi (ev.map (towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)) ≫ piComparison ev K)
    rw [AlgebraicGeometry.ProEtale.map_transition]
    exact inferInstance
  let S := ShortComplex.mk i t hz
  have : Mono S.f := mono_of_isLimit_fork hk
  have hS : S.ShortExact := { exact := S.exact_of_f_is_kernel hk }
  let S' := ShortComplex.mk i (-t) (by rw [Preadditive.comp_neg, hz, neg_zero])
  have hS' : S'.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := S) _ hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S, S']) (by simp [S, S'])
  have hq : QuasiIso (ExactProductsRoos.comparison.app I) :=
    AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S' hS'
      (ExactProductsRoos.comparison_condition I)
  have : IsIso (DerivedCategory.Q.map (ExactProductsRoos.comparison.app I)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 hq
  obtain ⟨e, he⟩ := ExactProductsRoos.comparisonIso L.R L.η L.computation
  have heI := NatTrans.congr_app he I
  change DerivedCategory.Q.map (ExactProductsRoos.comparison.app I) ≫ e.hom.app I =
    L.η.app I at heI
  rw [← heI]
  infer_instance

private theorem ordinaryRlim_isIso_of_unit
    {A : Type a} [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : DiagonalRlim A) (H : ℕᵒᵖ ⥤ A)
    (hη : IsIso (L.η.app ((HomologicalComplex.single (ℕᵒᵖ ⥤ A) (.up ℤ) 0).obj H))) :
    IsIso (diagonalOrdinaryRlim L H) := by
  have := hη
  unfold diagonalOrdinaryRlim
  infer_instance

/-- Epimorphic strict towers have invertible ordinary-to-derived limit comparison.

Source: the Milnor passage to the limit in the diagonal trace proof, paragraph (1).
(blueprint: new-sfb-diagonal-trace-ordinary-rlim-epi).

Proof: transfer the Milnor difference-map epimorphism and exact countable products
from modules over the constant ring sheaf. For the single complex of the tower,
the ordinary limit is the kernel of its degreewise epic difference map. The
zero-second-coordinate map into the Roos fibre is therefore a quasi-isomorphism.
The normalized Roos comparison identifies its localization with the given derived
unit, so every factor of the ordinary-to-derived comparison is invertible.
-/
private theorem ordinaryRlim_isIso_of_epi (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod l T)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l T)] (L : DiagonalRlim (DiagonalMod l T))
    (H : DiagonalSystems l T)
    (ht : ∀ n : ℕ, Epi (H.map (homOfLE (Nat.le_succ n)).op)) :
    IsIso (diagonalOrdinaryRlim L H) := by
  let I := (HomologicalComplex.single (DiagonalSystems l T) (.up ℤ) 0).obj H
  have hI (p : ℤ) (n : ℕ) : Epi ((I.X p).map (homOfLE (Nat.le_succ n)).op) := by
    by_cases hp : p = 0
    · subst p
      let e : I.X 0 ≅ H := HomologicalComplex.singleObjXSelf (.up ℤ) 0 H
      have := ht n
      have he := e.hom.naturality (homOfLE (Nat.le_succ n)).op
      have : Epi ((I.X 0).map (homOfLE (Nat.le_succ n)).op ≫ e.hom.app (op n)) := by
        rw [he]
        infer_instance
      exact (epi_comp_iff_of_isIso _ (e.hom.app (op n))).mp this
    · have hz : IsZero (I.X p) := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 H p hp
      exact ((Functor.isZero_iff _).mp hz (op n)).epi _
  have := towerProducts_exact l T
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l T) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod l T)
  have := derivedUnit_isIso L I (fun p ↦ towerDifference_epi l T (I.X p) (hI p))
  exact ordinaryRlim_isIso_of_unit L H inferInstance

private theorem diagonalRightDerived_exists
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] : Nonempty (DiagonalRightDerived F) := by
  obtain ⟨R, η, hu, hc, s, ht⟩ := CategoryTheory.RingedStrictTowerProof.totalDerivedData F
  let := s
  exact ⟨⟨R, η, hu, hc, ht⟩⟩

private theorem diagonalRightDerived_shift_exists
    {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type b} [Category.{u} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] :
    ∃ L : DiagonalRightDerived F, NatTrans.CommShift L.η ℤ := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let R := F.rightDerivedFunctor
  let e : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let η : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ R :=
    e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) R).hom
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) := by
    dsimp [η]
    infer_instance
  have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom =
        e.hom.app I.obj ≫ (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  let L : DiagonalRightDerived F :=
    { R := R
      η := η
      universal := hd.isRightDerivedFunctor_of_isIso η (fun I ↦ by
        have := I.property
        exact hi I.obj)
      computation I hI := hi I
      triangulated := inferInstance }
  refine ⟨L, ?_⟩
  have := CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift (DerivedCategory.quotientCompQhIso B).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (F.mapHomotopyCategoryFactors (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  dsimp only [L, η, e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

private theorem diagonalRlim_exists
    (A : Type a) [Category.{v} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)] : Nonempty (DiagonalRlim A) := by
  obtain ⟨L, hshift⟩ := diagonalRightDerived_shift_exists (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  have := L.universal
  let β (n : ℕ) :
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategory :=
    Functor.whiskerRight (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ))
        DerivedCategory.Q ≫ ((evaluation ℕᵒᵖ A).obj (op n)).mapDerivedCategoryFactors.inv
  let π (n : ℕ) := L.R.rightDerivedDesc L.η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) _ (β n)
  let := hshift
  refine ⟨{ toDiagonalRightDerived := L, projection := π, normalization := ?_ }⟩
  intro P n
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp [β]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem moduleRlim_exists (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod l X)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l X)] :
    Nonempty (DiagonalRlim (DiagonalMod l X)) := by
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) := by
    dsimp only [DiagonalMod]
    infer_instance
  have : IsGrothendieckAbelian.{u + 1} (DiagonalSystems l X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod l X)
  exact diagonalRlim_exists (DiagonalMod l X)

/-- An additive map into a module killed by `l ^ n` is `ℤ_[l]`-linear. -/
theorem padic_map_smul_target {l : ℕ} [Fact l.Prime]
    {M N : Type (u + 1)} [AddCommGroup M] [Module (ULift.{u + 1} ℤ_[l]) M]
    [AddCommGroup N] [Module (ULift.{u + 1} ℤ_[l]) N]
    (n : ℕ) (hN : ∀ y : N, (l ^ n) • y = 0) (f : M →+ N)
    (r : ULift.{u + 1} ℤ_[l]) (x : M) : f (r • x) = r • f x := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (r.down.appr_spec n)
  have hr : r - (r.down.appr n : ULift.{u + 1} ℤ_[l]) =
      (ULift.up a) * (l : ULift.{u + 1} ℤ_[l]) ^ n := by
    apply ULift.ext
    exact ha.symm
  have split (y : M) :
      r • y = (l ^ n) • (ULift.up a • y) + r.down.appr n • y := by
    conv_lhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
    rw [add_smul, mul_comm (ULift.up a), mul_smul]
    simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [split, map_add, map_nsmul, hN, zero_add, map_nsmul]
  conv_rhs => rw [← sub_add_cancel r (r.down.appr n : ULift.{u + 1} ℤ_[l]), hr]
  rw [add_smul, mul_comm (ULift.up a), mul_smul]
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hN, zero_add]

private theorem root_tower_killed (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (H : DiagonalSystems l X)
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime))
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : (H.obj (op n)).obj.obj U) :
    (l ^ (n + 1)) • x = 0 := by
  let e := roots.app (op n)
  have : Mono (e.hom.hom.app U) := by
    have : IsIso (e.hom.hom.app U) := by
      change IsIso (((sheafToPresheaf _ AddCommGrpCat).mapIso e).hom.app U)
      infer_instance
    infer_instance
  apply (AddCommGrpCat.mono_iff_injective (e.hom.hom.app U)).mp inferInstance
  change (e.hom.hom.app U) ((l ^ (n + 1)) • x) = (e.hom.hom.app U) 0
  rw [map_nsmul, map_zero]
  exact Scheme.proEtaleRootsOfUnity_nsmul X (l ^ (n + 1)) U _

private def liftToTorsion (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M N : DiagonalMod l X) (n : ℕ)
    (hN : ∀ (U : X.ProEtᵒᵖ) (x : N.obj.obj U), (l ^ (n + 1)) • x = 0)
    (f : (diagonalForget l X).obj M ⟶ (diagonalForget l X).obj N) : M ⟶ N :=
  ObjectProperty.homMk
    { app U := by
        let g : M.obj.obj U →+ N.obj.obj U := (f.hom.app U).hom
        exact ModuleCat.ofHom
          { toFun := g
            map_add' := g.map_add
            map_smul' z x := padic_map_smul_target (n + 1) (hN U) g z x }
      naturality U V g := by
        ext x
        exact ConcreteCategory.congr_hom (f.hom.naturality g) x }

/-- The prescribed abelian root-limit comparison lifts uniquely to a constant
p-adic module comparison, with exactly the prescribed underlying inverse.

Source: diagonal tower limit proof, paragraph (1), target ordinary limit.
(blueprint: lem-sfb-diagonal-root-limit-linear).

Proof: every finite root level is annihilated by the corresponding prime power.
An additive map into such a module is p-adic linear: approximate the scalar by
its integer residue and kill the error. Apply this to every coordinate of the
inverse abelian limit comparison. These lifted coordinates form a module cone.
Its unique limit lift has the prescribed underlying map because scalar forgetting
preserves limits and is faithful. That underlying map is invertible, and scalar
forgetting reflects isomorphisms, so the lift is invertible as well. -/
theorem root_limit_iso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (H : DiagonalSystems l X)
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) :
    ∃ t : (diagonalCompletedRestriction l X).obj (Scheme.purTwistZlModule X l) ≅ limit H,
      HEq ((diagonalForget l X).map t.hom)
        (diagonalRootLimitComparison l X H roots).inv := by
  let F := diagonalForget l X
  have : F.Faithful := by dsimp only [F, diagonalForget]; infer_instance
  have : F.ReflectsIsomorphisms := by dsimp only [F, diagonalForget]; infer_instance
  let M := (diagonalCompletedRestriction l X).obj (Scheme.purTwistZlModule X l)
  let e := diagonalRootLimitComparison l X H roots
  let g : F.obj M ⟶ F.obj (limit H) := by
    dsimp only [F, M, diagonalCompletedRestriction, diagonalForget,
      Scheme.purTwistZlModule, Scheme.purTwistZlOne]
    exact e.inv
  let c : Cone H :=
    { pt := M
      π :=
        { app := fun n ↦ liftToTorsion l X M (H.obj n) n.unop
            (root_tower_killed l X H roots n.unop) (g ≫ F.map (limit.π H n))
          naturality := by
            intro i j f
            apply F.map_injective
            change 𝟙 _ ≫ (g ≫ F.map (limit.π H j)) =
              (g ≫ F.map (limit.π H i)) ≫ F.map (H.map f)
            rw [Category.id_comp, Category.assoc, ← F.map_comp, limit.w] } }
  let t := limit.lift H c
  have ht : F.map t = g := by
    apply (isLimitOfPreserves F (limit.isLimit H)).hom_ext
    intro n
    change F.map t ≫ F.map (limit.π H n) = g ≫ F.map (limit.π H n)
    rw [← F.map_comp, limit.lift_π]
    rfl
  have hg : IsIso g := by
    change IsIso (id e.inv)
    exact (inferInstance : IsIso e.inv)
  have : IsIso (F.map t) := ht ▸ hg
  have : IsIso t := isIso_of_reflects_iso t F
  exact ⟨asIso t, heq_of_eq ht⟩

private theorem root_system_epi (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) (H : DiagonalSystems l X)
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (n : ℕ) :
    Epi (H.map (homOfLE (Nat.le_succ n)).op) := by
  let (x : X) : Invertible (l : X.residueField x) :=
    (show IsUnit (l : X.residueField x) from by
      let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map φ).invertible
  let U := diagonalForget l X
  have : U.Faithful := by dsimp only [U, diagonalForget]; infer_instance
  apply U.epi_of_epi_map
  have hroot : Epi ((Scheme.proEtaleRootsOfUnityTower X l
      (Fact.out : l.Prime)).map (homOfLE (Nat.le_succ n)).op) := by
    dsimp only [Scheme.proEtaleRootsOfUnityTower]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact Scheme.purTwistRootTransitions_epi X l n
  have he := roots.hom.naturality (homOfLE (Nat.le_succ n)).op
  change U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ roots.hom.app (op n) = _ at he
  have : Epi (U.map (H.map (homOfLE (Nat.le_succ n)).op) ≫ roots.hom.app (op n)) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (roots.hom.app (op n))).mp this

private theorem root_system_killed (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (H : DiagonalSystems l X)
    (roots : H ⋙ diagonalForget l X ≅
      Scheme.proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (n : ℕ) :
    l ^ (n + 1) • 𝟙 (H.obj (op n)) = 0 := by
  ext U x
  exact root_tower_killed l X H roots n U x

private theorem ordinary_tower_killed
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category B] [Abelian B] (l : ℕ) (F : A ⥤ B)
    (D : DiagonalReductionPresentation l F) (M : A) (n : ℕ) :
    (l ^ (n + 1)) • 𝟙 ((D.E.obj M).obj (op n)) = 0 := by
  have : Epi ((D.π n).app M) := Cofork.IsColimit.epi (D.quotient n M)
  apply (cancel_epi ((D.π n).app M)).mp
  simp only [Preadditive.comp_nsmul, comp_zero]
  erw [Category.comp_id]
  simpa only [Preadditive.nsmul_comp, Category.id_comp] using D.zero n M

private theorem ordinary_tower_epi
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category B] [Abelian B] (l : ℕ) (F : A ⥤ B)
    (D : DiagonalReductionPresentation l F) (M : A) (n : ℕ) :
    Epi ((D.E.obj M).map (homOfLE (Nat.le_succ n)).op) := by
  have : Epi ((D.π n).app M) := Cofork.IsColimit.epi (D.quotient n M)
  have : Epi ((D.π (n + 1)).app M ≫
      (D.E.obj M).map (homOfLE (Nat.le_succ n)).op) := by
    rw [D.transition]
    infer_instance
  exact epi_of_epi ((D.π (n + 1)).app M) _

private instance restrictScalars_products
    {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{b}] [J.WEqualsLocallyBijective AddCommGrpCat.{b}]
    {R S : Sheaf J RingCat.{b}} (r : R ⟶ S) :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.restrictScalars.{b} r) := by
  let F := SheafOfModules.restrictScalars.{b} r
  let G := SheafOfModules.forget.{b} R ⋙ PresheafOfModules.toPresheaf.{b} R.obj
  let U := SheafOfModules.forget.{b} S ⋙ PresheafOfModules.toPresheaf.{b} S.obj
  let e : F ⋙ G ≅ U := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)
  have : PreservesLimitsOfShape (Discrete ℕ) U := by dsimp only [U]; infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ G) :=
    preservesLimitsOfShape_of_natIso e.symm
  have : ReflectsLimitsOfShape (Discrete ℕ) G :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F G

private instance restrictScalars_reflectsIsos
    {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{b}} (r : R ⟶ S) :
    (SheafOfModules.restrictScalars.{b} r).ReflectsIsomorphisms := by
  constructor
  intro M N f hf
  have : IsIso ((SheafOfModules.toSheaf.{b} S).map f) :=
    inferInstanceAs (IsIso ((SheafOfModules.toSheaf.{b} R).map
      ((SheafOfModules.restrictScalars.{b} r).map f)))
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{b} S)

private instance completedRestriction_products (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    PreservesLimitsOfShape (Discrete ℕ) (diagonalCompletedRestriction l X) := by
  obtain ⟨e, he, _, _, _⟩ := (constant_ring_module_sheaves
    (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[l])).1
  have : (constantRingModuleRestriction (Scheme.ProEt.topology X)
      (ULift.{u + 1} ℤ_[l])).IsEquivalence := he ▸ e.isEquivalence_functor
  dsimp only [diagonalCompletedRestriction]
  infer_instance

private instance completedRestriction_reflectsIsos
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (diagonalCompletedRestriction l X).ReflectsIsomorphisms := by
  obtain ⟨e, he, _, _, _⟩ := (constant_ring_module_sheaves
    (Scheme.ProEt.topology X) (ULift.{u + 1} ℤ_[l])).1
  have : (constantRingModuleRestriction (Scheme.ProEt.topology X)
      (ULift.{u + 1} ℤ_[l])).IsEquivalence := he ▸ e.isEquivalence_functor
  dsimp only [diagonalCompletedRestriction]
  infer_instance

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ HasDerivedCategory.standard
  HomotopyCategory.singleFunctors Functor.mapDerivedCategorySingleFunctor

private theorem singleComparison_isIso
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H) (a : K ≅ (DerivedCategory.singleFunctor _ 0).obj H)
    [IsIso (diagonalOrdinaryRlim L H)] :
    IsIso (diagonalSingleLimitComparison F L P H K s a) := by
  unfold diagonalSingleLimitComparison
  infer_instance

private theorem shiftedComparison_isIso
    {A : Type a} [Category.{v} A] [Abelian A]
    {B : Type b} [Category B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H)
    (a : K ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    [IsIso (diagonalOrdinaryRlim L H)] :
    IsIso (diagonalShiftedSingleLimitComparison F L P H K s a) := by
  unfold diagonalShiftedSingleLimitComparison
  infer_instance

attribute [local irreducible] diagonalCompletedRestriction
  diagonalScalarExtension diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalDerivedSingleCounit

private theorem sourceLimitMap_isIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (diagonalCompletedSource l Y) ≅ limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (hs : IsIso (diagonalOrdinaryRlim L (D.ordinary.E.obj (diagonalIntegralSource Y)))) :
    IsIso (diagonalSourceLimitMap l Y D a L s) := by
  have := hs
  unfold diagonalSourceLimitMap
  exact singleComparison_isIso _ _ _ _ _ _ _

private theorem targetLimitMap_isIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l (diagonalSurface Y))]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (t : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (Scheme.purTwistZlModule (diagonalSurface Y) l) ≅ limit H)
    (hH : IsIso (diagonalOrdinaryRlim L H)) :
    IsIso (diagonalTargetLimitMap l Y D H b L t) := by
  have := hH
  unfold diagonalTargetLimitMap
  exact shiftedComparison_isIso _ _ _ _ _ _ _

-- Specialize the generic categorical theorem before inserting the concrete surface
-- and its two completed endpoints. This keeps the scalar-restriction instances shared.
private theorem completedEndpoints_orthogonal (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalCompleted l X)]
    [HasDerivedCategory.{u + 1} (DiagonalMod l X)]
    (n : ℤ) (P Q : DiagonalCompleted l X) (S H : DiagonalSystems l X)
    (s : (diagonalCompletedRestriction l X).obj P ≅ limit S)
    (t : (diagonalCompletedRestriction l X).obj Q ≅ limit H)
    (hS : ∀ r : ℕ, l ^ (r + 1) • 𝟙 (S.obj (op r)) = 0)
    (hH : ∀ r : ℕ, l ^ (r + 1) • 𝟙 (H.obj (op r)) = 0) :
    (∀ V : DerivedCategory (DiagonalCompleted l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (DerivedCategory.singleFunctor _ 0).obj P)) ∧
    (∀ V : DerivedCategory (DiagonalCompleted l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ ((DerivedCategory.singleFunctor _ 0).obj Q)⟦n⟧)) ∧
    (∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj
        ((DerivedCategory.singleFunctor _ 0).obj P))) ∧
    (∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj
        (((DerivedCategory.singleFunctor _ 0).obj Q)⟦n⟧))) := by
  have : IsGrothendieckAbelian.{u + 1} (DiagonalMod l X) := by
    dsimp only [DiagonalMod]
    infer_instance
  have : IsGrothendieckAbelian.{u + 1} (DiagonalCompleted l X) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  have : HasExactLimitsOfShape (Discrete ℕ) (DiagonalMod l X) := towerProducts_exact l X
  have : HasExactLimitsOfShape (Discrete ℕ) (DiagonalCompleted l X) :=
    Scheme.ProEt.products_exact.{u, 0, 0} X _ ℕ
  have : (diagonalCompletedRestriction l X).ReflectsIsomorphisms :=
    completedRestriction_reflectsIsos l X
  exact finite_tower_limit_orthogonality (diagonalCompletedRestriction l X)
    l n P Q S H s t hS hH

end AlgebraicGeometry.ProEtale.DiagonalEndpointsProof
