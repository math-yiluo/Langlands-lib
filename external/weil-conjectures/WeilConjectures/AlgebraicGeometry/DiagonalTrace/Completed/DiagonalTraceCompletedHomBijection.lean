/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Presentation.DiagonalTowerTracePresentations
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalCompleteScalarRestrictionCore
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Completed.DiagonalCompletedLineComplete
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Completed scalar restriction for the projective-line trace

Source: blueprint latest, diagonal-tower trace proof, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

open SpTowerClasses

private theorem complete_rightAdjoint
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R) (l : ℕ) (M : D)
    (hM : ∀ V : D, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ M)) :
    ∀ V : C, IsIso (l • 𝟙 V) → Subsingleton (V ⟶ R.obj M) := by
  intro V hV
  have : IsIso (l • 𝟙 (L.obj V)) := by
    have he : L.map (l • 𝟙 V) = l • 𝟙 (L.obj V) :=
      (L.map_nsmul).trans (congrArg (fun a ↦ l • a) (L.map_id V))
    rw [← he]
    exact L.map_isIso (l • 𝟙 V)
  have := hM (L.obj V) inferInstance
  exact (adj.homEquiv V M).symm.injective.subsingleton

private def rightDerivedComparison
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{u + 1} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{u + 1} B]
    (F : A ⥤ B) [F.Additive] (R : DiagonalRightDerived F) :
    R.R ≅ F.rightDerivedFunctor := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let η : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        F.rightDerivedFunctor).hom
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) := by
    dsimp [η]
    infer_instance
  have : F.rightDerivedFunctor.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := by
    apply (CategoryTheory.derives F).isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    exact hi I.obj
  have := R.universal
  exact Functor.rightDerivedUnique _ _ R.η η
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

/-- Completed scalar restriction is fully faithful on the two complete objects
used as the source and target of the trace.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), derived completeness
and passage from constant to completed coefficients; Stacks Tags 099I and 099L.
(blueprint: lem-sfb-diagonal-trace-completed-hom-bijection).

Proof: the completed unit and Tate line are derived l-complete. This may be checked
on the compatible-root pro-etale cover, where the line is the completed unit;
completeness is local. The unit hypothesis pulls back along f, so this cover
is available on X as well as S. Shifts preserve completeness. Derived direct image preserves
completeness: its right-adjoint description commutes with the derived limits in
the completion criterion, or equivalently its pullback carries l-invertible objects
to l-invertible objects. Thus Rc(completedLine(X)[2]) and completedUnit(S) are both
complete. The coefficient map from the constant Z_l sheaf to the completed ring
sheaf is flat and induces the canonical isomorphism at every finite quotient.
The constant/completed equivalence on derived-complete objects is induced by this
restriction functor. Its fullness and faithfulness give respectively surjectivity
and injectivity on the indicated ambient Hom set, since the subcategories of
complete objects are full. The specified Rc is a total derived direct image, so
its universal comparison identifies it with that used in this completeness
argument. No trace arrow is chosen and no finite reductions are used to assert
uniqueness of arbitrary derived morphisms. -/
theorem diagonalTrace_completedHom_bijective
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S]
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f)
    (hS : IsUnit (l : Γ(S, ⊤))) :
    Function.Bijective (fun t : p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧) ⟶
      completedUnit l S ↦ (diagonalCompletedUnderlying l S).map t)  := by
  let F := diagonalCompletedUnderlying l S
  let P : ObjectProperty (DerivedCategory (DiagonalCompleted l S)) := fun M ↦
    ∀ V : DerivedCategory (DiagonalMod l S),
      IsIso (l • 𝟙 V) → Subsingleton (V ⟶ F.obj M)
  obtain ⟨ff⟩ := diagonalCompleteScalarRestrictionCore l S
  let U := SheafOfModules.unit (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l))
  have hunit := diagonalCompletedLine_complete l S U
    ((SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one U).mp inferInstance)
  have hX : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hS.map f.appTop.hom
  let inst : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let ψ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map ψ).invertible
  have hfree : (Scheme.purTwistZlModule X l).IsFiniteLocallyFreeOfRank 1 :=
    (Scheme.pur_twist_sheaf_locally_free.{u, u} X l (ULift.{u} (Padic l))).2.1.2.1
  have hline₀ := diagonalCompletedLine_complete l X _ hfree
  let adjShift : shiftFunctor (DerivedCategory (DiagonalMod l X)) (-2 : ℤ) ⊣
      shiftFunctor (DerivedCategory (DiagonalMod l X)) (2 : ℤ) :=
    (shiftEquiv' (DerivedCategory (DiagonalMod l X))
      (-2 : ℤ) (2 : ℤ) (by decide)).toAdjunction
  have hshift := complete_rightAdjoint adjShift l
    ((diagonalCompletedUnderlying l X).obj (completedLine l X)) hline₀
  have hline : ∀ V : DerivedCategory (DiagonalMod l X), IsIso (l • 𝟙 V) →
      Subsingleton (V ⟶ (diagonalCompletedUnderlying l X).obj
        ((completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let e := Iso.homCongr (Iso.refl V)
      (((diagonalCompletedUnderlying l X).commShiftIso (2 : ℤ)).app
        (completedLine l X))
    constructor
    intro a b
    apply e.injective
    exact @Subsingleton.elim _ (hshift V hV) (e a) (e b)
  let adj := (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f).mapDerivedCategoryRightDerivedAdjunction
  let e := rightDerivedComparison _ p.Rf
  have hpush := complete_rightAdjoint adj l
    ((diagonalCompletedUnderlying l X).obj ((completedLine l X)⟦(2 : ℤ)⟧)) hline
  have hsource : P (p.Rc.R.obj ((completedLine l X)⟦(2 : ℤ)⟧)) := by
    intro V hV
    let c := (p.completed.iso.app ((completedLine l X)⟦(2 : ℤ)⟧)) ≪≫
      e.app ((diagonalCompletedUnderlying l X).obj ((completedLine l X)⟦(2 : ℤ)⟧))
    have := hpush V hV
    exact (Iso.homCongr (Iso.refl V) c).injective.subsingleton
  let A : P.FullSubcategory := ⟨_, hsource⟩
  let B : P.FullSubcategory := ⟨_, hunit⟩
  constructor
  · intro a b hab
    have hh : (ObjectProperty.homMk a : A ⟶ B) = ObjectProperty.homMk b :=
      ff.map_injective hab
    exact congrArg (fun h : A ⟶ B ↦ h.hom) hh
  · intro t
    obtain ⟨t', ht'⟩ := ff.map_surjective (X := A) (Y := B) t
    exact ⟨t'.hom, ht'⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
