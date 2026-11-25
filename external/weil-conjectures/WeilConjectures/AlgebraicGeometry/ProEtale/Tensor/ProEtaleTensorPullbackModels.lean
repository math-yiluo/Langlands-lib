/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalAdjunctionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels

/-!
# Canonical tensor pullback on the small pro-etale site

The object universe of the site is u+1 and its morphism universe is u.

## References

* Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E
* Modules on Sites, Tag 03EL
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf
  CategoryTheory.tensorPullbackTotal CategoryTheory.tensorPullbackTotalComponent

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
open SheafOfModules.CanonicalTensorPullbackOfUniverses

namespace AlgebraicGeometry.Scheme

/-- The ordinary sheaf tensor, with the original small pro-etale site. -/
noncomputable abbrev proEtaleOrdinaryTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  @curriedTensor (proEtaleRingModules X R) _ (SheafOfModules.monoidalCategory R)


/-- The flat-term K-flat representatives used in the ordinary uncompleted tensor. -/
def proEtaleFlatRepresentatives (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ObjectProperty (CochainComplex (proEtaleRingModules X R) ℤ) :=
  fun P ↦ P.IsAcyclicTensorKFlat ∧
    ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := R) (P.X n)

/-- A presentation of derived tensor by signed total tensor on flat K-flat complexes.
The representative isomorphism identifies the functor with the specified localization;
there is no completion or boundedness condition. -/
structure ProEtaleTensorModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) where
  tensor : DerivedCategory (proEtaleRingModules X R) ×
    DerivedCategory (proEtaleRingModules X R) ⥤ DerivedCategory (proEtaleRingModules X R)
  representative :
    ((proEtaleFlatRepresentatives X R).ι.prod (proEtaleFlatRepresentatives X R).ι) ⋙
      Functor.uncurry.obj ((proEtaleOrdinaryTensor X R).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
    (((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q).prod
      ((proEtaleFlatRepresentatives X R).ι ⋙ DerivedCategory.Q)) ⋙ tensor

/-- The section m tensor n in the sheafified tensor, using the existing sheafification. -/
noncomputable def proEtaleTensorPair (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : proEtaleRingModules X R) (U : X.ProEtᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((proEtaleOrdinaryTensor X R).obj M).obj N).val.obj U :=
  (SheafOfModules.tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{u + 1}
      (𝟙 ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit.app
          (M.val ⊗ N.val)).app U (m ⊗ₜ[R.obj.obj U] n))

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  SheafOfModules.monoidalCategory

private theorem modelTensorPair_restriction (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (M N : proEtaleRingModules X R) {U V : X.ProEtᵒᵖ} (i : U ⟶ V)
    (m : M.val.obj U) (n : N.val.obj U) :
    (((proEtaleOrdinaryTensor X R).obj M).obj N).val.map i
        (proEtaleTensorPair X R M N U m n) =
      proEtaleTensorPair X R M N V (M.val.map i m) (N.val.map i n) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let v := m ⊗ₜ[R.obj.obj U] n
  have hi := PresheafOfModules.naturality_apply
    (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).inv.val i
      ((adj.unit.app (M.val ⊗ N.val)).app U v)
  have hu := PresheafOfModules.naturality_apply (adj.unit.app (M.val ⊗ N.val)) i v
  exact hi.symm.trans
    (congrArg
      ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).inv.val.app V) hu.symm)

set_option backward.isDefEq.respectTransparency false in
private theorem modelTensor_hom_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {M N H : proEtaleRingModules X R}
    (a b : ((proEtaleOrdinaryTensor X R).obj M).obj N ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (m : M.val.obj U) (n : N.val.obj U),
      a.val.app U (proEtaleTensorPair X R M N U m n) =
        b.val.app U (proEtaleTensorPair X R M N U m n)) : a = b := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi
    (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).inv).1
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact h U m n
  | add t s ht hs => simp only [_root_.map_add, ht, hs]

private noncomputable def modelNormalizedAlgebraicLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    SheafOfModules.AlgebraicInverseImage
      (proEtaleSheafInverseImage f (Type (u + 1))) R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) :=
  { AlgebraicGeometry.ProEtaleTensorComparison.algebraicLift f R with
    modules := proEtaleModuleInverseImage f R }

private theorem modelNormalizedAlgebraicLift_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (P : proEtaleRingModules Y R)
    {T : Sheaf (ProEt.topology Y) (Type (u + 1))}
    (z : T ⟶ AlgebraicGeometry.ProEtaleTensorComparison.moduleSets P)
    (U : Y.ProEt) (t : T.obj.obj (Opposite.op U)) :
    ((proEtaleSheafInverseImage f (Type (u + 1))).map z ≫
        (modelNormalizedAlgebraicLift f R).moduleUnderlying.inv.app P).hom.app
          (Opposite.op ((proEtaleBaseChange f).obj U))
            (((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app T).hom.app
              (Opposite.op U) t) =
      AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f P U (z.hom.app _ t) := by
  exact AlgebraicGeometry.ProEtaleTensorComparison.algebraicLift_unit f P z U t

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Compare the full generalized pairing with the sectionwise adjunction formula.
/-- The ordinary comparison is uniquely determined by tensoring the canonical unit sections.
Naturality and the unit formula characterize the map on all local generators of inverse
image and scalar extension, including sections over objects not themselves base changes. -/
theorem proEtaleOrdinaryTensorPullback_existsUnique :
    ∃! mu : ∀ M N : proEtaleRingModules Y R,
      (proEtaleRingModulePullback f R S c).obj
          (((proEtaleOrdinaryTensor Y R).obj M).obj N) ≅
        ((proEtaleOrdinaryTensor X S).obj
          ((proEtaleRingModulePullback f R S c).obj M)).obj
            ((proEtaleRingModulePullback f R S c).obj N),
      (∀ (M M' N N' : proEtaleRingModules Y R) (v : M ⟶ M') (z : N ⟶ N'),
        (proEtaleRingModulePullback f R S c).map
            (((proEtaleOrdinaryTensor Y R).map v).app N ≫
              ((proEtaleOrdinaryTensor Y R).obj M').map z) ≫ (mu M' N').hom =
          (mu M N).hom ≫
            ((proEtaleOrdinaryTensor X S).map
              ((proEtaleRingModulePullback f R S c).map v)).app
                ((proEtaleRingModulePullback f R S c).obj N) ≫
            ((proEtaleOrdinaryTensor X S).obj
              ((proEtaleRingModulePullback f R S c).obj M')).map
                ((proEtaleRingModulePullback f R S c).map z)) ∧
      ∀ (M N : proEtaleRingModules Y R) (U : Y.ProEt)
        (m : M.val.obj (Opposite.op U)) (n : N.val.obj (Opposite.op U)),
        (mu M N).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f R S c).unit.app
              (((proEtaleOrdinaryTensor Y R).obj M).obj N)).val.app (Opposite.op U)
                (proEtaleTensorPair Y R M N (Opposite.op U) m n)) =
          proEtaleTensorPair X S ((proEtaleRingModulePullback f R S c).obj M)
            ((proEtaleRingModulePullback f R S c).obj N)
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (Opposite.op U) m)
            (((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app
              (Opposite.op U) n) := by
  classical
  let I := modelNormalizedAlgebraicLift f R
  let L := proEtaleRingModulePullback f R S c
  have hobj (M : proEtaleRingModules Y R) :
      L.obj M = SheafOfModules.changeOfRings c.hom (I.modules.obj M) := by
    rfl
  have hmap {M N : proEtaleRingModules Y R} (v : M ⟶ N) :
      L.map v = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c.hom (I.modules.obj M) (I.modules.map v) ≫
          eqToHom (hobj N).symm := by rfl
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  let k := Classical.choice
    (canonicalRingedTensorComparison_existsUnique.{u + 1, u} R S _
        (proEtaleSheafInverseImage f (Type (u + 1))) I c.hom L hobj
        (proEtaleSheafDirectImage f (Type (u + 1)))
        (proEtaleSheafAdjunction f (Type (u + 1))) hmap).1
  clear_value k
  have hunit (M : proEtaleRingModules Y R) (U : Y.ProEt) (m : M.val.obj (Opposite.op U)) :
      (k.q M).hom.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f M U m) =
        ((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (Opposite.op U) m := by
    apply Eq.trans (k.q_one M _ _)
    simp only [eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app]
    change proEtaleRingModuleUnitSection f R S c M U m = _
    exact (proEtaleRingModuleAdjunction_normalized f R S c M U m).symm
  have hpure (M N : proEtaleRingModules Y R) (U : Y.ProEt)
      (m : M.val.obj (Opposite.op U)) (n : N.val.obj (Opposite.op U)) :
      (k.mu M N).hom.val.app (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleRingModuleAdjunction f R S c).unit.app
            (((proEtaleOrdinaryTensor Y R).obj M).obj N)).val.app (Opposite.op U)
              (proEtaleTensorPair Y R M N (Opposite.op U) m n)) =
        proEtaleTensorPair X S (L.obj M) (L.obj N)
          (Opposite.op ((proEtaleBaseChange f).obj U))
          (((proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (Opposite.op U) m)
          (((proEtaleRingModuleAdjunction f R S c).unit.app N).val.app (Opposite.op U) n) := by
    let Z := MonoidalCategory.tensorObj
      (AlgebraicGeometry.ProEtaleTensorComparison.moduleSets M)
      (AlgebraicGeometry.ProEtaleTensorComparison.moduleSets N)
    let x : Z ⟶ AlgebraicGeometry.ProEtaleTensorComparison.moduleSets M :=
      CartesianMonoidalCategory.fst _ _
    let y : Z ⟶ AlgebraicGeometry.ProEtaleTensorComparison.moduleSets N :=
      CartesianMonoidalCategory.snd _ _
    let T := ((proEtaleOrdinaryTensor Y R).obj M).obj N
    let z : Z ⟶ AlgebraicGeometry.ProEtaleTensorComparison.moduleSets T :=
      AlgebraicGeometry.ProEtaleTensorComparison.binaryMap _ _ _
        (fun V a b ↦ proEtaleTensorPair Y R M N V a b)
        (fun i a b ↦ (modelTensorPair_restriction Y R M N i a b).symm) x y
    let W := Opposite.op ((proEtaleBaseChange f).obj U)
    let t : Z.obj.obj (Opposite.op U) := (m, n)
    let s := ((AlgebraicGeometry.ProEtale.setPullbackAdjunction f).unit.app Z).hom.app
      (Opposite.op U) t
    have hz (V) (a : Z.obj.obj V) :
        z.hom.app V a = proEtaleTensorPair Y R M N V (x.hom.app V a) (y.hom.app V a) := rfl
    let p0 := ((proEtaleSheafInverseImage f (Type (u + 1))).map z ≫
      I.moduleUnderlying.inv.app T).hom.app W s
    let m0 := ((proEtaleSheafInverseImage f (Type (u + 1))).map x ≫
      I.moduleUnderlying.inv.app M).hom.app W s
    let n0 := ((proEtaleSheafInverseImage f (Type (u + 1))).map y ≫
      I.moduleUnderlying.inv.app N).hom.app W s
    have h := k.pure M N Z x y z hz W s
    change (k.mu M N).hom.val.app W ((k.q T).hom.app W p0) =
      proEtaleTensorPair X S (L.obj M) (L.obj N) W
        ((k.q M).hom.app W m0) ((k.q N).hom.app W n0) at h
    have ht : p0 = AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f T U
        (proEtaleTensorPair Y R M N (Opposite.op U) m n) :=
      modelNormalizedAlgebraicLift_unit f T z U t
    have hm : m0 = AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f M U m :=
      modelNormalizedAlgebraicLift_unit f M x U t
    have hn : n0 = AlgebraicGeometry.ProEtaleTensorComparison.inverseSection f N U n :=
      modelNormalizedAlgebraicLift_unit f N y U t
    clear_value p0 m0 n0
    have hl := congrArg
      (fun v ↦ (k.mu M N).hom.val.app W ((k.q T).hom.app W v)) ht
    have hr := congrArg₂ (proEtaleTensorPair X S (L.obj M) (L.obj N) W)
      (congrArg ((k.q M).hom.app W) hm) (congrArg ((k.q N).hom.app W) hn)
    have hc := hl.symm.trans (h.trans hr)
    exact (congrArg ((k.mu M N).hom.val.app W)
      (hunit T U (proEtaleTensorPair Y R M N (Opposite.op U) m n)).symm).trans
        (hc.trans (congrArg₂ (proEtaleTensorPair X S (L.obj M) (L.obj N) W)
          (hunit M U m) (hunit N U n)))
  refine ⟨k.mu, ⟨?_, hpure⟩, ?_⟩
  · intro M M' N N' v z
    simpa only [proEtaleOrdinaryTensor, curriedTensor, tensorHom_def, Category.assoc]
      using k.naturality v z
  · intro mu hmu
    funext M N
    apply Iso.ext
    apply ((proEtaleRingModuleAdjunction f R S c).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply modelTensor_hom_ext Y R
    intro U m n
    exact (hmu.2 M N U.unop m n).trans (hpure M N U.unop m n).symm

attribute [local semireducible] SheafOfModules.monoidalCategory

/-- The canonical ordinary comparison, selected with its full unique characterization. -/
noncomputable def proEtaleOrdinaryTensorPullback :=
  Classical.choose (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists

/-- Naturality of the selected ordinary comparison, needed to form its signed total. -/
theorem proEtaleOrdinaryTensorPullback_naturality
    (M M' N N' : proEtaleRingModules Y R) (v : M ⟶ M') (z : N ⟶ N') :
    (proEtaleRingModulePullback f R S c).map
        (((proEtaleOrdinaryTensor Y R).map v).app N ≫
          ((proEtaleOrdinaryTensor Y R).obj M').map z) ≫
        (proEtaleOrdinaryTensorPullback f R S c M' N').hom =
      (proEtaleOrdinaryTensorPullback f R S c M N).hom ≫
        ((proEtaleOrdinaryTensor X S).map
          ((proEtaleRingModulePullback f R S c).map v)).app
            ((proEtaleRingModulePullback f R S c).obj N) ≫
        ((proEtaleOrdinaryTensor X S).obj
          ((proEtaleRingModulePullback f R S c).obj M')).map
            ((proEtaleRingModulePullback f R S c).map z) := by
  exact (Classical.choose_spec
    (proEtaleOrdinaryTensorPullback_existsUnique f R S c).exists).1 M M' N N' v z

attribute [local irreducible] proEtaleOrdinaryTensorPullback

/-- The inverse ordinary comparison, summed over every bidegree with the usual signs. -/
noncomputable def proEtaleTensorPullbackTotal
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    CochainComplex.mapBifunctor
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) (proEtaleOrdinaryTensor X S) ⟶
    ((proEtaleRingModulePullback f R S c).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (proEtaleOrdinaryTensor Y R)) := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact tensorPullbackTotal (proEtaleRingModulePullback f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) P Q

/-- The total comparison is invertible since pullback preserves its sum and summand maps. -/
theorem proEtaleTensorPullbackTotal_isIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :
    IsIso (proEtaleTensorPullbackTotal f R S c P Q) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  exact tensorPullbackTotal_isIso (proEtaleRingModulePullback f R S c)
    (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z)
    (proEtaleRingModuleDirectImage f R S c) (proEtaleRingModuleAdjunction f R S c) P Q

/-- The specified chain comparison as an isomorphism. -/
noncomputable def proEtaleTensorPullbackTotalIso
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  @asIso _ _ _ _ (proEtaleTensorPullbackTotal f R S c P Q)
    (proEtaleTensorPullbackTotal_isIso f R S c P Q)

end AlgebraicGeometry.Scheme
