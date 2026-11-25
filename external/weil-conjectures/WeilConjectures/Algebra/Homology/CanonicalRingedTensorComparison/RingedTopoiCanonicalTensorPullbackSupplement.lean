/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
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
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitUnique
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback

/-!
# Canonical representative comparison for tensor pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
  [MonoidalPreadditive A] [MonoidalPreadditive B]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B]
  (L : A ⥤ B) [L.Additive]
  (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)

universe wA wB

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Transport the homotopy right-derived comparison to the complex localization Q.
Source: Stacks 070K (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def derivedPushforwardComplexComparison
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (V : B ⥤ A) [V.Additive] (RF : DerivedCategory B ⥤ DerivedCategory A)
    (eta : V.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) (K : CochainComplex B ℤ) :
    DerivedCategory.Q.obj ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      RF.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso A).inv.app
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    DerivedCategory.Qh.map ((V.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      eta.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K) ≫
        RF.map ((DerivedCategory.quotientCompQhIso B).hom.app K)

end CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

universe w

section TensorSections

attribute [local irreducible] monoidalCategory

open scoped ChangeOfRings TensorProduct
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
  (A B : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private theorem productElements {E : Type u} [Category.{v} E] [HasBinaryProducts E]
    (F : E ⥤ Type v) (X Y : E) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

variable (c : A ⟶ B)

@[no_expose] private noncomputable def ins (M : SheafOfModules.{u} (𝓡 A))
    (W : Dᵒᵖ) (m : M.val.obj W) : (changeOfRings.{u, u, u} c M).val.obj W :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} c M)).app W
      ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))
-- Expand the two scalar extensions through the sheafification adjunction.
end TensorSections

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

section TensorUniqueness

attribute [local irreducible] monoidalCategory

set_option backward.isDefEq.respectTransparency.types false

-- Compare bilinear maps through sheafification and the scalar-extension adjunctions.
end TensorUniqueness

/-- Chain-level representative of the canonical comparison.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.total [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    CochainComplex.mapBifunctor
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)
      (@curriedTensor (SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) _ (monoidalCategory S)) ⟶
    (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mapBifunctor P Q (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC
      (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) _ (monoidalCategory R))) := by
  letI := monoidalCategory R
  letI := monoidalCategory S
  letI := ringedTensorPreadditive R
  letI := ringedTensorPreadditive S
  exact tensorPullbackTotal L k.mu k.naturality P Q

/-- The specified total comparison is an isomorphism.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: its summand maps are the inverse ordinary comparisons. Pullback is a left
adjoint and preserves the coproducts defining total complexes. Thus each component
is an isomorphism, and so is the chain map. -/
theorem CanonicalRingedTensorComparison.total_isIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :
    IsIso (k.total R S RI uInv I c L hobj P Q) := by
  let := monoidalCategory R
  let := monoidalCategory S
  let := ringedTensorPreadditive R
  let := ringedTensorPreadditive S
  exact tensorPullbackTotal_isIso L k.mu k.naturality V am P Q

/-- The canonical chain comparison as an isomorphism, with no arbitrary choice.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback). -/
noncomputable def CanonicalRingedTensorComparison.totalIso [L.Additive]
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am : L ⊣
      V)
    (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) :=
  @asIso _ _ _ _ (k.total R S RI uInv I c L hobj P Q)
    (k.total_isIso R S RI uInv I c L hobj V am P Q)

attribute [local irreducible] CanonicalRingedTensorComparison.totalIso monoidalCategory

namespace CanonicalTensorPullbackProof

open CategoryTheory.Functor in
set_option synthInstance.maxSize 2048 in
private theorem tensorMap_factor
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap f (𝟙 Q) (curriedTensor A) (.up ℤ) ≫
      HomologicalComplex.mapBifunctorMap (𝟙 P') g (curriedTensor A) (.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ) := by
  simp [HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

open CategoryTheory.Functor in
set_option synthInstance.maxSize 2048 in
private theorem tensorPullbackTotal_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    {P P' Q Q' : CochainComplex A ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    HomologicalComplex.mapBifunctorMap
      ((L.mapHomologicalComplex (.up ℤ)).map f)
      ((L.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor B) (.up ℤ) ≫
        tensorPullbackTotal L e he P' Q' =
      tensorPullbackTotal L e he P Q ≫ (L.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)) := by
  have hi {X X' Y Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
      (L.map a ⊗ₘ L.map b) ≫ (e X' Y').inv =
        (e X Y).inv ≫ L.map (a ⊗ₘ b) := by
    apply (cancel_mono (e X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he, Iso.inv_hom_id_assoc]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, tensorPullbackTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  simp only [Category.assoc]
  change (L.map (f.f a) ▷ L.obj (Q.X b)) ≫
    (L.obj (P'.X a) ◁ L.map (g.f b)) ≫ _ = _
  rw [← tensorHom_def_assoc]
  change (L.map (f.f a) ⊗ₘ L.map (g.f b)) ≫ (e (P'.X a) (Q'.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P' Q' (curriedTensor A) a b n hab) =
    (e (P.X a) (Q.X b)).inv ≫
      L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n hab) ≫
        L.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor A) (.up ℤ)).f n)
  rw [← Category.assoc, hi, Category.assoc, ← L.map_comp]
  congr 2
  rw [← L.map_comp]
  congr 1
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rw [tensorHom_def, Category.assoc]
  rfl

private noncomputable def tensorPullbackTotalNatIso
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    {B : Type u'} [Category.{v'} B] [Abelian B] [MonoidalCategory B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [HasCoproducts.{0} A] [HasCoproducts.{0} B]
    (L : A ⥤ B) [L.Additive]
    (e : ∀ X Y : A, L.obj (X ⊗ Y) ≅ L.obj X ⊗ L.obj Y)
    (he : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      L.map (f ⊗ₘ g) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (L.map f ⊗ₘ L.map g))
    (V : B ⥤ A) (am : L ⊣ V) :
    let F := L.mapHomologicalComplex (.up ℤ)
    let tA := Functor.uncurry.obj ((curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
    let tB := Functor.uncurry.obj ((curriedTensor B).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
    (F.prod F) ⋙ tB ≅ tA ⋙ F := by
  refine NatIso.ofComponents (fun X ↦
    @asIso _ _ _ _ (tensorPullbackTotal L e he X.1 X.2)
      (tensorPullbackTotal_isIso L e he V am X.1 X.2)) ?_
  intro X Y f
  simp only [asIso_hom, Functor.comp_map, Functor.prod_map, Functor.uncurry_obj_map,
    Functor.map₂HomologicalComplex, tensorMap_factor]
  exact tensorPullbackTotal_naturality L e he f.1 f.2

end CanonicalTensorPullbackProof

set_option synthInstance.maxSize 2048 in
set_option linter.style.longLine false in
/-- Canonical derived comparison, uniquely characterized on K-flat flat-term representatives.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
Proof: resolve both inputs by K-flat flat-term complexes; pullback preserves that class
by 0G7E. Their total tensor is K-flat by reassociating an acyclic test tensor and applying
K-flatness twice, and has flat terms by tensor-flatness and countable flat sums.
The left-derived comparison computes pullback on these representatives. Compose it
with the inverse image of the explicit chain comparison k.totalIso and rS. The displayed
square records exactly this construction relative to rR. Naturality of the summand
comparisons handles both differentials and their signs. Two-variable tensor descent
extends the square to all derived objects and makes its extension unique. The ordinary
unit normalization is canonicalRingedTensorComparison_unit, forced by k.pure. -/
theorem ringedTopoiCanonicalDerivedTensorPullback
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V) :
    (∀ P : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        CochainComplex.IsAcyclicTensorKFlat
          ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
          ∀ n : ℤ,
            (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat) ∧
    ∃! alpha : TR ⋙ LF ≅ (LF.prod LF) ⋙ TS,
      ∀ (P Q : CochainComplex (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ) (hp : PR P) (hq : PR Q),
        ∃ (hp' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hq' : PS ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          LF.map (rR.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
              alpha.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
                TS.map (CategoryTheory.Prod.mkHom
                  (derivedPullbackComplexComparison uStar LF epsilon P)
                  (derivedPullbackComplexComparison uStar LF epsilon Q)) =
            derivedPullbackComplexComparison uStar LF epsilon
              (CochainComplex.mapBifunctor P Q
                (@curriedTensor (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) _ (monoidalCategory R))) ≫
              (DerivedCategory.Q.mapIso
                (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv ≫
                  rS.hom.app
                    (⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P, hp'⟩,
                      ⟨(uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q, hq'⟩) := by
  have hpres : ∀ P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      P.IsAcyclicTensorKFlat →
      (∀ n : ℤ, (P.X n).IsFlat) →
      CochainComplex.IsAcyclicTensorKFlat
        ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat := by
    intro P hp hf
    have hf' : ∀ n, IsFlatOnSite (J := JC) (R := R) (P.X n) := fun n ↦
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm (hf n)
    obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback
      uInv uPush adj I c uStar hobj hmap P hp hf'
    exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso S _) (ht n)⟩
  let A := SheafOfModules.{u}
    ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let B := SheafOfModules.{u}
    ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)
  let F := uStar.mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((@curriedTensor A _ (monoidalCategory R)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((@curriedTensor B _ (monoidalCategory S)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let eps : DerivedCategory.Q ⋙ LF ⟶ F ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv LF ≫
      Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) epsilon ≫
      Functor.whiskerRight (uStar.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft F (DerivedCategory.quotientCompQhIso B).hom
  have hF : ∀ P, PR P → PS (F.obj P) := by
    intro P hp
    exact (hPS _).2 (hpres P ((hPR _).1 hp).1 ((hPR _).1 hp).2)
  have hder := ringedTopoiDerivedPullback uInv uPush adj I c uStar hobj hmap
  let LF' := hder.choose
  let ε' := hder.choose_spec.choose
  have hLF' := hder.choose_spec.choose_spec.1
  have hε' := hder.choose_spec.choose_spec.2.2.2.1
  have := hLF
  have := hLF'
  let e := Functor.leftDerivedNatIso LF' LF ε' epsilon
    (HomotopyCategory.quasiIso A (.up ℤ)) (Iso.refl _)
  have he (P : CochainComplex A ℤ) (hp : P.IsAcyclicTensorKFlat)
      (hf : ∀ n : ℤ, (P.X n).IsFlat) : IsIso (eps.app P) := by
    have : IsIso (ε'.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) :=
      hε' P hp hf
    have hfac : e.hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
        epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
          ε'.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
      simp [e, Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans_app]
    have heps : IsIso (epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := by
      have : IsIso (e.hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
          epsilon.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := by
        rw [hfac]
        infer_instance
      exact IsIso.of_isIso_comp_left (e.hom.app _) (epsilon.app _)
    dsimp only [eps, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    infer_instance
  have het (P Q : CochainComplex A ℤ) (hp : P.IsAcyclicTensorKFlat)
      (hf : ∀ n : ℤ, (P.X n).IsFlat) (hq : Q.IsAcyclicTensorKFlat)
      (hqf : ∀ n : ℤ, (Q.X n).IsFlat) : IsIso (eps.app (tR.obj (P, Q))) := by
    have ht := KFlatTotalTensorModel.kFlat_total_tensor_model R P Q hp hq
      (fun n ↦ (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso R (P.X n)).symm (hf n))
      (fun n ↦ (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso R (Q.X n)).symm (hqf n))
    exact he _ ht.1 (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R _) (ht.2.1 n))
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := by
    let := monoidalCategory R
    let := monoidalCategory S
    let := ringedTensorPreadditive R
    let := ringedTensorPreadditive S
    exact CanonicalTensorPullbackProof.tensorPullbackTotalNatIso uStar k.mu k.naturality V am
  let b := b0.symm
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ PR X.as
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : H.FullSubcategory) (f : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) f := by
    intro X
    obtain ⟨P, f, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients X.as
    have hflat : ∀ n, (P.X n).IsFlat := hf
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, (hPR P).2 ⟨hp, hflat⟩⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map f, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hq
  set_option backward.isDefEq.respectTransparency true in
    have hff := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
      (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
      (D := DerivedCategory A) (DerivedCategory B)
      (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
      (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff := hff.some
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  set_option backward.isDefEq.respectTransparency true in
    have hdes := CategoryTheory.tensorComparisonDescent
      (K := CochainComplex A ℤ) (H := CochainComplex B ℤ)
      (D := DerivedCategory A) (E := DerivedCategory B)
      DerivedCategory.Q DerivedCategory.Q F LF eps PR PS hF ff' tR tS TR TS rR rS b
      (fun P hp ↦ he P ((hPR _).1 hp).1 ((hPR _).1 hp).2)
      (fun P Q hp hq ↦ het P Q ((hPR _).1 hp).1 ((hPR _).1 hp).2
        ((hPR _).1 hq).1 ((hPR _).1 hq).2)
  have heps (P : CochainComplex A ℤ) :
      eps.app P = derivedPullbackComplexComparison uStar LF epsilon P := rfl
  have hb (P Q : CochainComplex A ℤ) :
      DerivedCategory.Q.map (b.hom.app (P, Q)) =
        (DerivedCategory.Q.mapIso
          (k.totalIso R S RI uInv I c uStar hobj V am P Q)).inv := by
    change DerivedCategory.Q.map (b0.app (P, Q)).inv =
      DerivedCategory.Q.map (k.totalIso R S RI uInv I c uStar hobj V am P Q).inv
    apply congrArg DerivedCategory.Q.map
    apply (Iso.inv_eq_inv _ _).2
    delta CanonicalRingedTensorComparison.totalIso
    rfl
  refine ⟨hpres, (existsUnique_congr ?_).mp hdes⟩
  intro alpha
  constructor
  · intro ha P Q hp hq
    refine ⟨hF P hp, hF Q hq, ?_⟩
    have hh := ha P Q hp hq
    simp only [heps, hb] at hh
    exact hh
  · intro ha P Q hp hq
    set_option backward.isDefEq.respectTransparency true in
      have hh := (ha P Q hp hq).choose_spec.choose_spec
    simp only [heps, hb]
    exact hh

set_option synthInstance.maxSize 2048 in
-- Keep both tensor representative interfaces explicit.
/-- The canonical derived comparison selected by its unique representative characterization.
Source: Stacks 07A4 (blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).
The theorem specifies the natural isomorphism uniquely, so only its proof is postponed. -/
noncomputable def ringedTopoiCanonicalDerivedTensorComparison
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{u}} {S RI : Sheaf JD CommRingCat.{u}}
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uPush : Sheaf JD (Type u) ⥤ Sheaf JC (Type u))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R), uStar.obj M = changeOfRings
        c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : M ⟶ N), uStar.map a =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫
        eqToHom (hobj N).symm)
    [uStar.Additive]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (LF : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (epsilon : DerivedCategory.Qh ⋙ LF ⟶
      uStar.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (hLF : LF.IsLeftDerivedFunctor epsilon
      (HomotopyCategory.quasiIso (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (ComplexShape.up ℤ)))
    (PR : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ))
    (PS : ObjectProperty (CochainComplex (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ))
    (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (hPS : ∀ P, PS P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
    (TR : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (TS : (DerivedCategory (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) × (DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))) ⥤ DerivedCategory
      (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
          (SheafOfModules.monoidalCategory R)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    (rS : (PS.ι.prod PS.ι) ⋙ Functor.uncurry.obj
        ((@CategoryTheory.MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) _
          (SheafOfModules.monoidalCategory S)).map₂HomologicalComplex
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
      ((PS.ι ⋙ DerivedCategory.Q).prod (PS.ι ⋙ DerivedCategory.Q)) ⋙ TS)
    (k : CanonicalRingedTensorComparison R S RI uInv I c uStar hobj)
    (V : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (am :
      uStar ⊣ V) :
    TR ⋙ LF ≅ (LF.prod LF) ⋙ TS :=
  Classical.choose (ringedTopoiCanonicalDerivedTensorPullback
    (C := C) (D := D) (JC := JC) (JD := JD) (R := R) (S := S) (RI := RI)
    uInv uPush adj I c uStar
    hobj hmap LF epsilon hLF PR PS hPR hPS TR TS rR rS k V am).2.exists

end SheafOfModules
