/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf

import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
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
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedCounit
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedLocalizationSequence
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedFilteredColimits

/-!
# Ringed pro-etale open-closed localization

## References

* Stacks, Modules on Sites, Tag 03D1
* Stacks, Tags 09A5 and 03D6
* Stacks, Tags 09AA, 09BM, 09BN, 09AH, 09AG, 03DI, 03DJ and 0738
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The underlying ring sheaf of arbitrary commutative pro-etale coefficients. -/
noncomputable abbrev proEtaleModuleCoefficients {X : Scheme.{u}}
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

/-- Direct image with action through the inverse-image adjunction unit. On sections
it is evaluation on the base change; on morphisms it retains the same linear components. -/
noncomputable def proEtaleRingedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := proEtaleModuleCoefficients A)
    (R := proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A))
    ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Extension by zero in the localized presentation of the open site's ringed topos.
The presheaf is the sum over factorizations through `U`, with its actual module action;
sheafification is the existing module sheafification. For a monic open immersion the
index set is empty or a singleton. No finiteness restriction is placed on coefficients. -/
noncomputable def proEtaleRingedExtensionByZero {X : Scheme.{u}} (U : X.ProEt)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.extensionByZeroPresheaf.{u + 1} (proEtaleModuleCoefficients A) U ⋙
    PresheafOfModules.sheafification (𝟙 (proEtaleModuleCoefficients A).obj)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def proEtaleModuleModelEquivalence (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≌
      SheafOfModules.{u + 1} A := by
  let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj A
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (ProEt.topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (ProEt.topology X)
    infer_instance
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 A) (𝟙 B)
    (by ext U; dsimp [AsSmall.equiv]; erw [B.obj.map_id]; rfl)
    (by ext U; dsimp [AsSmall.equiv]; erw [A.obj.map_id]; rfl)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ringedInverseImageAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleModuleInverseImage f R ⊣ proEtaleRingedDirectImage f R := by
  let A := proEtaleModuleCoefficients R
  let B := proEtaleModuleCoefficients
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let eY := proEtaleModuleModelEquivalence Y A
  let eX := proEtaleModuleModelEquivalence X B
  let adj := eY.symm.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction (proEtaleModelRingUnit f R)).comp
      eX.toAdjunction)
  change proEtaleModuleInverseImage f R ⊣ _ at adj
  apply adj.ofNatIsoRight
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
  · intro M N a
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

end AlgebraicGeometry.Scheme

namespace SheafOfModules

open Classical in
private theorem extensionRestrict_of
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) {V W : Cᵒᵖ} (a : V ⟶ W)
    (φ : V.unop ⟶ U) (ψ : W.unop ⟶ U) (h : a.unop ≫ φ = ψ)
    (x : F.val.obj (Opposite.op (Over.mk φ))) :
    extensionByZeroPresheafRestrictAdd R U F a
        (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) =
      DirectSum.of (fun χ : W.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk χ))) ψ
        (F.val.map (Opposite.op (Over.homMk a.unop h : Over.mk ψ ⟶ Over.mk φ)) x) := by
  subst ψ
  change (DirectSum.toAddMonoid _)
    (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x) = _
  rw [DirectSum.toAddMonoid_of]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionPresheafToHom
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) :
    F ⟶ (overFunctor R U).obj G where
  val.app X := ModuleCat.ofHom
    ((a.app (Opposite.op X.unop.left)).hom.comp
      (DirectSum.lof (R.obj.obj (Opposite.op X.unop.left)) (X.unop.left ⟶ U)
        (fun φ ↦ F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom))
  val.naturality {X Y} f := by
    ext x
    have h := PresheafOfModules.naturality_apply a
      ((Over.forget U).op.map f)
      (DirectSum.of _ X.unop.hom x)
    change a.app (Opposite.op Y.unop.left)
        (extensionByZeroPresheafRestrictAdd R U F ((Over.forget U).op.map f)
          (DirectSum.of _ X.unop.hom x)) = _ at h
    have hr := extensionRestrict_of R U F ((Over.forget U).op.map f)
      X.unop.hom Y.unop.hom (Over.w f.unop) x
    erw [hr] at h
    have hf : (Over.homMk f.unop.left (Over.w f.unop) : Y.unop ⟶ X.unop) =
        f.unop := by ext; rfl
    erw [hf] at h
    change a.app (Opposite.op Y.unop.left)
        (DirectSum.of (fun φ : Y.unop.left ⟶ U ↦
          F.val.obj (Opposite.op (Over.mk φ))) Y.unop.hom (F.val.map f x)) =
      G.val.map ((Over.forget U).op.map f)
        (a.app (Opposite.op X.unop.left)
          (DirectSum.of (fun φ : X.unop.left ⟶ U ↦
            F.val.obj (Opposite.op (Over.mk φ))) X.unop.hom x))
    exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionHomToPresheaf
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : F ⟶ (overFunctor R U).obj G) :
    extensionByZeroPresheafObj R U F ⟶ G.val where
  app V := ModuleCat.ofHom (DirectSum.toModule _ _ _
    (fun φ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
  naturality {V W} f := by
    ext x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of φ x =>
      change (DirectSum.toModule (R.obj.obj W) _ (G.val.obj W)
        (fun ψ : W.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
        (extensionByZeroPresheafRestrictAdd R U F f
          (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x)) =
          G.val.map f ((DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom))
            (DirectSum.of (fun ψ : V.unop ⟶ U ↦ F.val.obj (Opposite.op (Over.mk ψ))) φ x))
      erw [extensionRestrict_of R U F f φ (f.unop ≫ φ) rfl]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      exact PresheafOfModules.naturality_apply a.val
        (Opposite.op (Over.homMk f.unop : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ)) x
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionPresheafHomEquiv
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R) :
    (extensionByZeroPresheafObj R U F ⟶ G.val) ≃
      (F ⟶ (overFunctor R U).obj G) where
  toFun := extensionPresheafToHom R U F G
  invFun := extensionHomToPresheaf R U F G
  left_inv a := by
    ext V x
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun φ : V.unop ⟶ U ↦ (a.app V).hom.comp
        (DirectSum.lof (R.obj.obj V) _ _ φ))) x = (a.app V) x
    exact (DirectSum.toModule.unique _ (a.app V).hom x).symm
  right_inv a := by
    ext X x
    change (DirectSum.toModule (R.obj.obj (Opposite.op X.unop.left)) _
      (G.val.obj (Opposite.op X.unop.left))
      (fun φ : X.unop.left ⟶ U ↦ (a.val.app (Opposite.op (Over.mk φ))).hom))
        (DirectSum.lof _ _ _ X.unop.hom x) = (a.val.app X) x
    erw [DirectSum.toModule_lof]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheafHomEquiv_naturality_right
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F : SheafOfModules.{u + 1} (R.over U)) (G H : SheafOfModules.{u + 1} R)
    (a : extensionByZeroPresheafObj R U F ⟶ G.val) (b : G ⟶ H) :
    extensionPresheafHomEquiv R U F H (a ≫ b.val) =
      extensionPresheafHomEquiv R U F G a ≫ (overFunctor R U).map b := by
  ext X x
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
private theorem extensionPresheafHomEquiv_naturality_left_symm
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (F H : SheafOfModules.{u + 1} (R.over U)) (G : SheafOfModules.{u + 1} R)
    (a : H ⟶ F) (b : F ⟶ (overFunctor R U).obj G) :
    (extensionPresheafHomEquiv R U H G).symm (a ≫ b) =
      (extensionByZeroPresheaf R U).map a ≫
        (extensionPresheafHomEquiv R U F G).symm b := by
  ext V x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of φ x =>
    change (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
      (fun ψ : V.unop ⟶ U ↦ ((a ≫ b).val.app (Opposite.op (Over.mk ψ))).hom))
        (DirectSum.of _ φ x) =
      (DirectSum.toModule (R.obj.obj V) _ (G.val.obj V)
        (fun ψ : V.unop ⟶ U ↦ (b.val.app (Opposite.op (Over.mk ψ))).hom))
          (DirectSum.lmap (R := R.obj.obj V)
            (fun ψ : V.unop ⟶ U ↦ (a.val.app (Opposite.op (Over.mk ψ))).hom)
              (DirectSum.of _ φ x))
    erw [DirectSum.lmap_of, DirectSum.toModule_lof, DirectSum.toModule_lof]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

-- Fix the coefficient universe of the locally bijective criterion; the generic instance
-- leaves a universe metavariable for the essential smallness of the site.
private instance extensionAbWEqualsLocallyBijective {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  @SheafOfModules.wEqualsLocallyBijective_coefficientUniverse C _ (essentiallySmallSelf.{0} C) J

set_option backward.isDefEq.respectTransparency false in
private noncomputable def extensionSheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C) :
    (extensionByZeroPresheaf.{u + 1} R U ⋙
      PresheafOfModules.sheafification.{u + 1} (𝟙 R.obj)) ⊣ overFunctor.{u + 1} R U := by
  refine Adjunction.mkOfHomEquiv ?_
  refine
    { homEquiv := fun F G ↦
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
          (extensionPresheafHomEquiv R U F G)
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro H F G a b
    change (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
        ((extensionPresheafHomEquiv R U H G).symm (a ≫ b)) = _
    rw [extensionPresheafHomEquiv_naturality_left_symm]
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left_symm
      ((extensionByZeroPresheaf R U).map a)
      ((extensionPresheafHomEquiv R U F G).symm b)
    have heq (P : PresheafOfModules.{u + 1} R.obj) (G : SheafOfModules.{u + 1} R) :
        (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv P G =
          PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) := by
      apply Equiv.ext
      intro f
      exact PresheafOfModules.sheafificationAdjunction_homEquiv_apply _ f
    rw [heq, heq] at h
    exact h
  · intro F G H a b
    change extensionPresheafHomEquiv R U F H
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b)) = _
    have h := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_right
      a b
    change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (a ≫ b) =
      PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) a ≫ b.val at h
    erw [h]
    exact extensionPresheafHomEquiv_naturality_right R U F G H _ b

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionSectionIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U V : C) [Subsingleton (V ⟶ U)] (φ : V ⟶ U)
    (F : SheafOfModules.{u + 1} (R.over U)) :
    F.val.obj (op (Over.mk φ)) ≅ (extensionByZeroPresheaf R U).obj F |>.obj (op V) := by
  exact LinearEquiv.toModuleIso
    { toLinearMap := DirectSum.lof (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      invFun := DirectSum.component (R.obj.obj (op V)) (V ⟶ U)
        (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ
      left_inv := by
        intro x
        exact DirectSum.component.lof_self (M := fun ψ ↦ F.val.obj (op (Over.mk ψ)))
          (R.obj.obj (op V)) φ x
      right_inv := by
        intro x
        induction x using DirectSum.induction_on with
        | zero => simp
        | of ψ x =>
          have : ψ = φ := Subsingleton.elim _ _
          subst ψ
          change DirectSum.lof _ _ _ φ (DirectSum.component _ _ _ φ
            (DirectSum.lof (R.obj.obj (op V)) _
              (fun ψ ↦ F.val.obj (op (Over.mk ψ))) φ x)) = _
          rw [DirectSum.component.lof_self]
          rfl
        | add x y hx hy =>
          change DirectSum.of _ φ (x φ + y φ) = x + y
          rw [map_add]
          exact congrArg₂ (· + ·) hx hy }

set_option backward.isDefEq.respectTransparency false in
private theorem extensionPresheaf_preservesFiniteLimits
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U)) :
    PreservesFiniteLimits (extensionByZeroPresheaf.{u + 1} R U) := by
  classical
  let L := extensionByZeroPresheaf.{u + 1} R U
  let T := PresheafOfModules.toPresheaf.{u + 1} R.obj
  have : PreservesFiniteLimits (L ⋙ T) := by
    apply preservesFiniteLimits_of_evaluation
    intro V
    let E := (L ⋙ T) ⋙ (CategoryTheory.evaluation _ _).obj V
    let := hU V.unop
    by_cases h : Nonempty (V.unop ⟶ U)
    · obtain ⟨φ⟩ := h
      let D := evaluation.{u + 1} (R.over U) (op (Over.mk φ)) ⋙
        forget₂ (ModuleCat (R.obj.obj V)) AddCommGrpCat.{u + 1}
      let e : D ≅ E := NatIso.ofComponents (fun F ↦
        (forget₂ (ModuleCat (R.obj.obj V)) AddCommGrpCat.{u + 1}).mapIso
          (extensionSectionIso R U V.unop φ F)) (by
        intro F G f
        ext x
        apply DFinsupp.ext
        intro ψ
        have hψ : ψ = φ := Subsingleton.elim _ _
        subst ψ
        simp [D, E, L, T, extensionSectionIso, LinearEquiv.toModuleIso,
          extensionByZeroPresheaf, extensionByZeroPresheafHom,
          extensionByZeroPresheafHomApp, extensionByZeroPresheafObj,
          extensionByZeroPresheafSection, evaluation, PresheafOfModules.evaluation,
          PresheafOfModules.toPresheaf, forget, DirectSum.lof, DFinsupp.lsingle,
          DirectSum.lmap, DFinsupp.mapRange.linearMap]
        simp only [DFunLike.coe]
        simp only [DFinsupp.toFun_eq_coe, DFinsupp.mapRange_apply, DFinsupp.single_eq_same]
        rfl)
      exact preservesFiniteLimits_of_natIso e
    · let : IsEmpty (V.unop ⟶ U) := not_nonempty_iff.mp h
      have hz : IsZero E := E.isZero (fun F ↦ by
        change IsZero (AddCommGrpCat.of (DirectSum (V.unop ⟶ U)
          (fun φ ↦ F.val.obj (op (Over.mk φ)))))
        let : Subsingleton (DirectSum (V.unop ⟶ U)
            (fun φ ↦ F.val.obj (op (Over.mk φ)))) :=
          ⟨fun x y ↦ by ext φ; exact isEmptyElim φ⟩
        exact (IsZero.iff_id_eq_zero _).2 (by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          exact Subsingleton.elim _ _))
      have : PreservesLimitsOfSize.{0, 0} E := E.preservesLimitsOfSize_of_isZero hz
      infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves L T

set_option backward.isDefEq.respectTransparency false in
open Classical in
private noncomputable def extensionRestrictionIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{u + 1} (R.over U)) :
    ((SheafOfModules.toSheaf (R.over U)).obj F).obj ≅
      (Over.forget U).op ⋙ ((extensionByZeroPresheaf R U).obj F).presheaf := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · let := hU V.unop.left
    exact (forget₂ (ModuleCat (R.obj.obj (op V.unop.left))) AddCommGrpCat).mapIso
      (extensionSectionIso R U V.unop.left V.unop.hom F)
  · intro V W a
    let := hU V.unop.left
    let := hU W.unop.left
    ext x
    change _ = extensionByZeroPresheafRestrictAdd R U F
      ((Over.forget U).op.map a) (DirectSum.of _ V.unop.hom x)
    erw [extensionRestrict_of R U F ((Over.forget U).op.map a)
      V.unop.hom W.unop.hom (by exact a.unop.w)]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem extensionSheafAdjunction_unit_isIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u + 1}) (U : C)
    (hU : ∀ V : C, Subsingleton (V ⟶ U))
    (F : SheafOfModules.{u + 1} (R.over U)) :
    IsIso ((extensionSheafAdjunction R U).unit.app F) := by
  let P := ((extensionByZeroPresheaf R U).obj F).presheaf
  let T := (Over.forget U).op ⋙ P
  have hT : Presheaf.IsSheaf (J.over U) T :=
    (Presheaf.isSheaf_of_iso_iff (extensionRestrictionIso R U hU F)).mp
      ((SheafOfModules.toSheaf _).obj F).property
  have : IsIso (toSheafify (J.over U) T) := isIso_toSheafify _ hT
  have hh := (Over.forget U).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u + 1} (J.over U) J P
  have : IsIso (Functor.whiskerLeft (Over.forget U).op (toSheafify J P)) := by
    rw [← hh]
    infer_instance
  let η := (extensionSheafAdjunction R U).unit.app F
  have hη : ((SheafOfModules.toSheaf _).map η).hom =
      (extensionRestrictionIso R U hU F).hom ≫
        Functor.whiskerLeft (Over.forget U).op (toSheafify J P) := by
    ext V x
    rfl
  have : IsIso ((sheafToPresheaf (J.over U) AddCommGrpCat.{u + 1}).map
      ((SheafOfModules.toSheaf _).map η)) := by
    change IsIso (((SheafOfModules.toSheaf _).map η).hom)
    rw [hη]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map η) :=
    isIso_of_reflects_iso _ (sheafToPresheaf (J.over U) AddCommGrpCat.{u + 1})
  exact isIso_of_reflects_iso η (SheafOfModules.toSheaf _)

end SheafOfModules

namespace CategoryTheory

private theorem leftAdjointComposite_isZero.{v, w}
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [HasZeroMorphisms D]
    (L : C ⥤ D) (R : D ⥤ C) (F : E ⥤ C) (J : C ⥤ E)
    (ai : L ⊣ R) (aj : F ⊣ J) (hzero : ∀ H, IsZero (J.obj (R.obj H)))
    (G : E) : IsZero (L.obj (F.obj G)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (ai.homEquiv _ _).injective
  apply (aj.homEquiv _ _).injective
  exact (hzero _).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
private theorem closed_preservesFiniteColimits.{v, w}
    {C D E : Type v} [Category.{w} C] [Category.{w} D] [Category.{w} E]
    [Abelian C] [Abelian D] [Abelian E]
    (L : C ⥤ D) (R : D ⥤ C) (J : C ⥤ E) (ai : L ⊣ R)
    [L.PreservesZeroMorphisms] [J.PreservesZeroMorphisms]
    [PreservesFiniteColimits L] [PreservesFiniteColimits J]
    (hc : ∀ H, IsIso (ai.counit.app H))
    (hz : ∀ H, IsZero (J.obj (R.obj H)))
    (hd : ∀ M, IsZero (L.obj M) → IsZero (J.obj M) → IsZero M) :
    PreservesFiniteColimits R := by
  have : PreservesLimitsOfSize.{0, 0} R := ai.rightAdjoint_preservesLimits
  have : PreservesBinaryBiproducts R :=
    preservesBinaryBiproducts_of_preservesBinaryProducts R
  have : R.Additive := R.additive_of_preservesBinaryBiproducts
  have : R.PreservesEpimorphisms := by
    constructor
    intro H H' f hf
    let c := cokernel.π (R.map f)
    have hL : Epi (L.map (R.map f)) := by
      have he : L.map (R.map f) = ai.counit.app H ≫ f ≫ inv (ai.counit.app H') := by
        apply (cancel_mono (ai.counit.app H')).1
        simpa only [Functor.comp_map, Functor.id_map, Category.assoc,
          IsIso.inv_hom_id, Category.comp_id] using ai.counit.naturality f
      rw [he]
      infer_instance
    have hLQ : IsZero (L.obj (cokernel (R.map f))) := by
      apply IsZero.of_epi_eq_zero (L.map c)
      apply zero_of_epi_comp (L.map (R.map f))
      rw [← L.map_comp]
      change L.map (R.map f ≫ cokernel.π (R.map f)) = _
      rw [cokernel.condition, L.map_zero]
    have hJQ : IsZero (J.obj (cokernel (R.map f))) := by
      apply IsZero.of_epi_eq_zero (J.map c)
      exact (hz H').eq_of_src _ _
    exact Preadditive.epi_of_isZero_cokernel (R.map f) (hd _ hLQ hJQ)
  have : R.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels R
  exact Functor.preservesFiniteColimits_of_preservesHomology R

end CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem open_closed_directImage_isZero {X Z : Scheme.{u}} (i : Z ⟶ X)
    (U : X.ProEt) [IsOpenImmersion U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (H : SheafOfModules.{u + 1} (proEtaleModuleCoefficients
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A))) :
    IsZero ((SheafOfModules.overFunctor.{u + 1}
      (proEtaleModuleCoefficients A) U).obj ((proEtaleRingedDirectImage i A).obj H)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let W := (proEtaleBaseChange i).obj V.unop.left
  have hsubset : Set.range V.unop.left.hom ⊆ Set.range U.hom := by
    rintro _ ⟨v, rfl⟩
    exact ⟨V.unop.hom.left v, congrArg (fun f : V.unop.left.left ⟶ X ↦ f v)
      V.unop.hom.w⟩
  have hdisj : Disjoint (Set.range V.unop.left.hom) (Set.range i) := by
    rw [Set.disjoint_left]
    intro x hx hxi
    exact (hU ▸ hsubset hx) hxi
  let : IsEmpty W.left := Scheme.isEmpty_pullback V.unop.left.hom i hdisj
  let HH := (SheafOfModules.toSheaf _).obj H
  have hz := (HH.isTerminalOfBotCover W (ProEt.bot_mem_topology W)).isZero
  let : Subsingleton (HH.obj.obj (op W)) := AddCommGrpCat.subsingleton_of_isZero hz
  change (x : HH.obj.obj (op W)) = 0
  exact @Subsingleton.elim (HH.obj.obj (op W)) inferInstance _ _

/-- Open-closed localization with arbitrary ring-sheaf coefficients. The open part
is presented on the slice `X.ProEt / U`, as in the weakly-etale localization theorem:
its ring is `A.over U`, and inverse image is `overFunctor`. The closed part uses the
actual inverse-image ring and the base-change direct image. -/
theorem proEtale_ringed_open_closed {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : SheafOfModules.{u + 1} (proEtaleModuleCoefficients
        ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)) ≌
          SheafOfModules.{u + 1} ((proEtaleModuleCoefficients A).over U),
      Nonempty (proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅
        SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U) ∧
    ∃ (ai : proEtaleModuleInverseImage i A ⊣ proEtaleRingedDirectImage i A)
      (aj : proEtaleRingedExtensionByZero U A ⊣
        SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U),
      (∀ H, IsIso (ai.counit.app H)) ∧
      (∀ G, IsIso (aj.unit.app G)) ∧
      (∀ H, IsZero ((SheafOfModules.overFunctor.{u + 1}
        (proEtaleModuleCoefficients A) U).obj ((proEtaleRingedDirectImage i A).obj H))) ∧
      (∀ G, IsZero ((proEtaleModuleInverseImage i A).obj
        ((proEtaleRingedExtensionByZero U A).obj G))) ∧
      PreservesFiniteLimits (proEtaleRingedExtensionByZero U A) ∧
      PreservesFiniteColimits (proEtaleRingedExtensionByZero U A) ∧
      PreservesFiniteLimits (proEtaleRingedDirectImage i A) ∧
      PreservesFiniteColimits (proEtaleRingedDirectImage i A) ∧
      (∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
        (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact) ∧
      (CompactSpace X → QuasiSeparatedSpace X →
        ∀ (I : Type (u + 1)) [SmallCategory I] [IsFiltered I],
          PreservesColimitsOfShape I (proEtaleRingedDirectImage i A)) := by
  let ai := ringedInverseImageAdjunction i A
  let aj := SheafOfModules.extensionSheafAdjunction (proEtaleModuleCoefficients A) U
  have hsub : ∀ V : X.ProEt, Subsingleton (V ⟶ U) := by
    intro V
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono U.hom).1
    exact f.w.trans g.w.symm
  have hu := SheafOfModules.extensionSheafAdjunction_unit_isIso
    (proEtaleModuleCoefficients A) U hsub
  obtain ⟨q, hq⟩ := proEtale_ringed_open_comparison U A
  obtain ⟨e⟩ := hq
  have hc := proEtale_ringed_closed_counit i A ai
  have hz := open_closed_directImage_isZero i U hU A
  have hs := proEtale_ringed_localization_sequence i U hU A ai aj
  have : PreservesLimitsOfSize.{0, 0} (proEtaleRingedDirectImage i A) :=
    ai.rightAdjoint_preservesLimits
  have : PreservesColimitsOfSize.{0, 0} (proEtaleRingedExtensionByZero U A) :=
    aj.leftAdjoint_preservesColimits
  have : PreservesLimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U) :=
    aj.rightAdjoint_preservesLimits
  have : (proEtaleRingedExtensionByZero U A).IsLeftAdjoint := aj.isLeftAdjoint
  have : (proEtaleRingedDirectImage i A).IsRightAdjoint := ai.isRightAdjoint
  have : (SheafOfModules.overFunctor.{u + 1}
      (proEtaleModuleCoefficients A) U).IsRightAdjoint := aj.isRightAdjoint
  have : PreservesFiniteLimits (proEtaleRingedExtensionByZero U A) := by
    change PreservesFiniteLimits (_ ⋙ _)
    have := SheafOfModules.extensionPresheaf_preservesFiniteLimits
      (proEtaleModuleCoefficients A) U hsub
    infer_instance
  obtain ⟨haddj, _, hcolj, _⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits U.hom).2.2 A
  have := haddj
  have := hcolj
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u + 1} (proEtaleModuleCoefficients A) U) :=
    preservesFiniteColimits_of_natIso e
  obtain ⟨haddi, _, hcoli, _⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits i).2.2 A
  have := haddi
  have := hcoli
  have hd : ∀ M, IsZero ((proEtaleModuleInverseImage i A).obj M) →
      IsZero ((SheafOfModules.overFunctor.{u + 1}
        (proEtaleModuleCoefficients A) U).obj M) → IsZero M := by
    intro M hi hj
    let S := ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)
    have hS : S.Exact := (hs M).2.2
    have he := (S.exact₂_iff hS.toIsComplex).1 hS
    exact he.isZero_of_both_isZero
      ((proEtaleRingedExtensionByZero U A).map_isZero hj)
      ((proEtaleRingedDirectImage i A).map_isZero hi)
  have : PreservesFiniteColimits (proEtaleRingedDirectImage i A) :=
    CategoryTheory.closed_preservesFiniteColimits _ _ _ ai hc hz hd
  refine ⟨q, ⟨e⟩, ai, aj, hc, hu, hz, ?_, inferInstance, inferInstance,
    inferInstance, inferInstance, hs, ?_⟩
  · exact CategoryTheory.leftAdjointComposite_isZero _ _ _ _ ai aj hz
  · intro hqc hqs I _ _
    have := hqc
    have := hqs
    exact proEtale_ringed_filtered_colimits i A I

end AlgebraicGeometry.Scheme
