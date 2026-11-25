/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
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
import Mathlib.CategoryTheory.Sites.Limits
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
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageRestrictionOfScalars
import Mathlib.CategoryTheory.Whiskering

/-!
# Stratum pullback and scalar-extension comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md,
  proof paragraph (2), expanded constant-module pullback and stratum tensor comparison
(blueprint: lem-sp-stratum-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The map of constant coefficient rings induced by a unital map of rings.
Source: the coefficient comparison in the scalar-extension proof (blueprint:
`lem-sp-stratum-scalar-extension`). -/
noncomputable def proEtaleConstantRingMap {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift α))

/-- A constant module presheaf is left adjoint to evaluation at a terminal object.
Source: the constant-sheaf universal property, Stacks Tag 0H7J. -/
private noncomputable def constantPresheafHomEquiv (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} A))
    (F : PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) :
    (proEtaleConstantModulePresheaf Y.ProEt A M ⟶ F) ≃ (M ⟶ F.obj (op T)) where
  toFun f := f.app (op T)
  invFun q :=
    { app U := q ≫ F.map (hT.from U.unop).op
      naturality := by
        intro U V a
        ext x
        symm
        change F.map a (F.map (hT.from U.unop).op (q x)) =
          F.map (hT.from V.unop).op (q x)
        rw [← F.map_comp_apply]
        have h : (hT.from U.unop).op ≫ a = (hT.from V.unop).op := by
          change (a.unop ≫ hT.from U.unop).op = _
          exact congrArg Quiver.Hom.op (hT.hom_ext _ _)
        rw [h] }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op x).symm
  right_inv q := by
    have h : hT.from T = 𝟙 T := hT.hom_ext _ _
    ext x
    change F.map (hT.from T).op (q x) = q x
    rw [h]
    simp
    rfl
private noncomputable def constantPF (Y : Scheme.{u}) (A : Type u) [CommRing A] :
    ModuleCat.{u + 1} (ULift.{u + 1} A) ⥤ PresheafOfModules.{u + 1}
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)) ⋙
        forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) where
  obj M := proEtaleConstantModulePresheaf Y.ProEt A M
  map f := { app _ := f, naturality := by intros; ext x; rfl }
  map_id _ := by apply PresheafOfModules.hom_ext; intro U; rfl
  map_comp _ _ := by apply PresheafOfModules.hom_ext; intro U; rfl

private noncomputable def constantPFAdj (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) (hT : IsTerminal T) :
    constantPF Y A ⊣ PresheafOfModules.evaluation _ (op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv Y A T hT
      homEquiv_naturality_left_symm := by
        intros
        apply PresheafOfModules.hom_ext
        intro U
        rfl
      homEquiv_naturality_right := by intros; rfl }

private noncomputable def ringUnit (Y : Scheme.{u}) (A : Type u) [CommRing A] :=
  Functor.whiskerRight (toSheafify (ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})

private noncomputable def constantGlobal (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (T : Y.ProEt) :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} A) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (ringUnit Y A) ⋙
    PresheafOfModules.evaluation _ (op T)

section ScalarComparison

variable (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (α : A →+* B)

private noncomputable def scalarPresheafFunctor :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      PresheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (proEtaleConstantRing X B)).obj where
  obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (proEtaleConstantRingMap (T := X) α)
  map a :=
    { app := fun U ↦ (ModuleCat.extendScalars
        ((proEtaleConstantRingMap (T := X) α).hom.app U).hom).map (a.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ _ a }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    simp
    rfl
  map_comp a b := by
    apply PresheafOfModules.hom_ext
    intro U
    simp

private noncomputable def scalarFunctor :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X B) :=
  scalarPresheafFunctor X α ⋙ PresheafOfModules.sheafification
    (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).obj (proEtaleConstantRing X B)).obj)

private noncomputable def scalarAdjunction :
    scalarFunctor X α ⊣ proEtaleCoefficientRestrictScalars X α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α)
      homEquiv_naturality_left_symm := by
        intro M M' N k h
        apply (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N).injective
        change (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N)
          ((SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N).symm
            (k ≫ h)) =
          (SheafOfModules.changeHomEquiv (proEtaleConstantRingMap (T := X) α) M N)
            (SheafOfModules.changeOfRingsHom (proEtaleConstantRingMap (T := X) α) M k ≫
              (SheafOfModules.changeHomEquiv
                (proEtaleConstantRingMap (T := X) α) M' N).symm h)
        exact (Equiv.apply_symm_apply _ _).trans
          ((SheafOfModules.changeHomEquiv_naturality_left
            (proEtaleConstantRingMap (T := X) α) M M' N k
            ((SheafOfModules.changeHomEquiv
              (proEtaleConstantRingMap (T := X) α) M' N).symm h)).trans
                (congrArg (fun z ↦ k ≫ z) (Equiv.apply_symm_apply _ _))).symm
      homEquiv_naturality_right := fun h k ↦
        SheafOfModules.changeHomEquiv_naturality_right _ _ _ _ k h }

section
variable {T S : Scheme.{u}} (i : S ⟶ T) (A B : Type u)
  [CommRing A] [CommRing B] [Finite A] [Finite B] (α : A →+* B)

end
end ScalarComparison

-- The composite adjunction and dependent module transports require extra elaboration steps.
end AlgebraicGeometry.Scheme
