/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option linter.privateModule false

/-! # Derived scalar extension of locally finite free module sheaves

Source: Stacks Project, Modules on Sites, Tags 0GN1 and 08FC; Cohomology on Sites,
Tags 06YQ and 06YY (blueprint: lem-sfb-locally-free-derived-scalars).

The ordinary functor and its universal derived comparison are those of
`DerivedChangeOfRingsCochainModel`. Its object and map equations fix ordinary extension
as sheafification of sectionwise scalar extension, with the new ring acting on the left.
The degree-zero comparison below is its counit followed by the standard single-complex
isomorphism. In particular it is not an arbitrarily selected isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u v r wR wB

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarUnitIso
    {B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) :
    changeOfRings φ (unit (derivedChangeRingIndependentCoefficients J R)) ≅
      unit (derivedChangeRingIndependentCoefficients J B) := by
  let O := derivedChangeRingIndependentCoefficients J R
  let A := derivedChangeRingIndependentCoefficients J B
  let e (V : Cᵒᵖ) :
      (changeOfRingsPresheaf φ (unit O)).obj V ≅ (unit A).val.obj V := by
    let := (φ.hom.app V).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj V)
      (B.obj.obj V) (B.obj.obj V)).toModuleIso
  let ep : changeOfRingsPresheaf φ (unit O) ≅ (unit A).val :=
    PresheafOfModules.isoMk e (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (e Y).hom (changeOfRingsMap φ (unit O) f
        ((1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x)) =
          B.obj.map f ((e X).hom
            ((1 : B.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] x))
      erw [Classical.choose_spec (exists_changeOfRingsMap φ (unit O) f) 1 x, map_one]
      change (φ.hom.app Y) (R.obj.map f x) * 1 =
        B.obj.map f ((φ.hom.app X) x * 1)
      simp only [mul_one]
      exact ConcreteCategory.congr_hom (φ.hom.naturality f) x)
  exact (PresheafOfModules.sheafification.{r} (R := A) (𝟙 _)).mapIso ep ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)).counit.app (unit A))

-- Scalar extension commutes with restriction to the slice. The underlying
-- presheaves have identical pure tensors, and slice sheafification supplies the iso.
open scoped ChangeOfRings in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def scalarOverIso
    {B : Sheaf J CommRingCat.{r}} (φ : R ⟶ B)
    (M : ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}] :
    (changeOfRings φ M).over U ≅
      changeOfRings ((J.overPullback CommRingCat.{r} U).map φ) (M.over U) := by
  let ψ := (J.overPullback CommRingCat.{r} U).map φ
  let A := derivedChangeRingIndependentCoefficients J B
  let P := changeOfRingsPresheaf φ M
  let ep : changeOfRingsPresheaf ψ (M.over U) ≅
      (PresheafOfModules.pushforward.{r} (F := Over.forget U) (𝟙 _)).obj P :=
    PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro X Y f
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change changeOfRingsMap ψ (M.over U) f
        ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
          (φ.hom.app (Opposite.op X.unop.left)).hom] x) =
        changeOfRingsMap φ M ((Over.forget U).op.map f)
          ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
            (φ.hom.app (Opposite.op X.unop.left)).hom] x)
      rw [show changeOfRingsMap ψ (M.over U) f
          ((1 : B.obj.obj (Opposite.op X.unop.left)) ⊗ₜ[_,
            (φ.hom.app (Opposite.op X.unop.left)).hom] x) = _ from
          Classical.choose_spec (exists_changeOfRingsMap ψ (M.over U) f) 1 x]
      exact (Classical.choose_spec
        (exists_changeOfRingsMap φ M ((Over.forget U).op.map f)) 1 x).symm)
  have := overSheafificationMap_isIso.{u, v, r, r} A U P
  exact ((PresheafOfModules.sheafification.{r} (R := A.over U) (𝟙 _)).mapIso ep ≪≫
    asIso (overSheafificationMap.{u, v, r, r} A U P)).symm

end SheafOfModules
