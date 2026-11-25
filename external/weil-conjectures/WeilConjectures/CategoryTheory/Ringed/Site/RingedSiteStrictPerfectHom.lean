/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
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
import WeilConjectures.SixFunctors.Supporting.RingedSiteHomComponentProjection
import WeilConjectures.CategoryTheory.RingedSiteBoundedDual.RingedSiteBoundedDualComponents
import WeilConjectures.CategoryTheory.RingedSiteBoundedEvaluation.RingedSiteBoundedEvaluationAssembly
import WeilConjectures.Algebra.Homology.Ringed.RingedSiteFiniteRetractDualExact
import WeilConjectures.CategoryTheory.SplitPerfectHom.IndependentBoundedExactTermHom
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart

/-! # Ordinary Hom calculations for a bounded finite-free retract complex

Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ,
lemma-Rhom-strictly-perfect and lemma-dual-perfect-complex.
(blueprint: lem-sfb-ringed-site-strict-perfect-hom).
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.RingedSiteBoundedDual.modulesHasZeroObject
  CategoryTheory.RingedSiteBoundedEvaluation.smallColimits
  CategoryTheory.RingedSiteBoundedEvaluation.hasTotal
  CategoryTheory.RingedSiteBoundedEvaluation.finiteBiproducts
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace PresheafOfModules

private noncomputable local instance spRestrictedSMul
    {D : Type c} [Category.{v} D] {S : Dᵒᵖ ⥤ CommRingCat.{r}}
    (M : PresheafOfModules.{r} (S ⋙ forget₂ _ _)) (U : Dᵒᵖ) (W : (Over U.unop)ᵒᵖ) :
    SMul (((restrictOver S U.unop).obj (unit (S ⋙ forget₂ _ _))).obj W)
      ((ModuleCat.restrictScalars
        ((S ⋙ forget₂ CommRingCat RingCat).map W.unop.hom.op).hom).obj
          (M.obj (op W.unop.left))) :=
  (M.obj (op W.unop.left)).isModule.toSMul

variable {C : Type c} [Category.{v} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{max c v r}}
  (N : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _))

private lemma sp_homObjUnitIsoApp_hom_apply (X : Cᵒᵖ) (φ : (homObj (unit _) N).obj X) :
    (chart_homObjUnitIsoApp.{c, v, r} (R := R) N X).hom φ = φ.app (op (Over.mk (𝟙 X.unop))) (1 :
      R.obj X) :=
  rfl

open MonoidalCategory in
private noncomputable def sp_scalarEvaluation
    (A B : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _)) :
    B ⊗ homObj A (unit _) ⟶ homObj A B where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun y φ ↦ φ ≫ chart_homObjUnitInvApp.{c, v, r} (R := R) B y)
    (by
      intro y z φ
      apply hom_ext (M₁ := (restrictOver R U.unop).obj A)
        (M₂ := (restrictOver R U.unop).obj B)
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s : R.obj (op W.unop.left) := (φ.app W).hom x
      change s • (show B.obj (op W.unop.left) from B.map W.unop.hom.op (y + z)) =
        s • (show B.obj (op W.unop.left) from B.map W.unop.hom.op y) +
          s • (show B.obj (op W.unop.left) from B.map W.unop.hom.op z)
      rw [map_add]
      exact smul_add s _ _)
    (by
      intro a y φ
      apply hom_ext (M₁ := (restrictOver R U.unop).obj A)
        (M₂ := (restrictOver R U.unop).obj B)
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s : R.obj (op W.unop.left) := (φ.app W).hom x
      change s • (show B.obj (op W.unop.left) from B.map W.unop.hom.op (a • y)) =
        R.map W.unop.hom.op a •
          (s • (show B.obj (op W.unop.left) from B.map W.unop.hom.op y))
      rw [B.map_smul]
      exact smul_comm s (R.map W.unop.hom.op a)
        (show B.obj (op W.unop.left) from B.map W.unop.hom.op y))
    (by
      intro y φ ψ
      apply hom_ext (M₁ := (restrictOver R U.unop).obj A)
        (M₂ := (restrictOver R U.unop).obj B)
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s : R.obj (op W.unop.left) := (φ.app W).hom x
      let t : R.obj (op W.unop.left) := (ψ.app W).hom x
      let z : B.obj (op W.unop.left) := B.map W.unop.hom.op y
      change (s + t) • z = s • z + t • z
      exact add_smul s t z)
    (by
      intro a y φ
      apply hom_ext (M₁ := (restrictOver R U.unop).obj A)
        (M₂ := (restrictOver R U.unop).obj B)
      intro W
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      let s : R.obj (op W.unop.left) := (φ.app W).hom x
      let z : B.obj (op W.unop.left) := B.map W.unop.hom.op y
      change (R.map W.unop.hom.op a * s) • z = R.map W.unop.hom.op a • (s • z)
      exact (mul_smul (R.map W.unop.hom.op a) s z))
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro y φ
    apply hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let s : R.obj (op W.unop.left) :=
      (φ.app (op ((Over.map f.unop).obj W.unop))).hom x
    change s • (show B.obj (op W.unop.left) from
      B.map W.unop.hom.op (B.map f y)) =
        s • (show B.obj (op W.unop.left) from B.map (W.unop.hom ≫ f.unop).op y)
    rw [← map_comp_apply]
    rfl

private lemma sp_scalarEvaluation_apply
    (A B : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _)) (U : Cᵒᵖ)
    (y : B.obj U) (φ : (homObj A (unit _)).obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A.obj (op W.unop.left)) :
    (((sp_scalarEvaluation.{c, v, r} (R := R) A B).app U
      (y ⊗ₜ[R.obj U] φ)).app W).hom x =
      (φ.app W).hom x • B.map W.unop.hom.op y := by
  rfl

open MonoidalCategory in
private theorem sp_scalarEvaluation_unit_isIso
    (B : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _)) :
    IsIso (sp_scalarEvaluation.{c, v, r} (R := R) (unit _) B) := by
  let O : PresheafOfModules.{max c v r} (R ⋙ forget₂ _ _) := unit _
  have heq : sp_scalarEvaluation.{c, v, r} (R := R) O B =
      B ◁ (chart_homObjUnitIso.{c, v, r} (R := R) O).hom ≫ (ρ_ B).hom ≫
        (chart_homObjUnitIso.{c, v, r} (R := R) B).inv := by
    apply hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro y φ
    have hφ : φ = chart_homObjUnitInvApp.{c, v, r} (R := R) O
        ((chart_homObjUnitIsoApp.{c, v, r} (R := R) O U).hom φ) := by
      exact (ConcreteCategory.congr_hom
        (chart_homObjUnitIsoApp.{c, v, r} (R := R) O U).hom_inv_id φ).symm
    rw [hφ]
    apply hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change R.obj (op W.unop.left) at x
    change (x * (show R.obj (op W.unop.left) from O.map W.unop.hom.op _)) •
      (show B.obj (op W.unop.left) from B.map W.unop.hom.op y) =
      x • (show B.obj (op W.unop.left) from B.map W.unop.hom.op
        ((show R.obj U from (chart_homObjUnitIsoApp.{c, v, r} (R := R) O U).hom
          (chart_homObjUnitInvApp.{c, v, r} (R := R) O _)) • y))
    simp only [sp_homObjUnitIsoApp_hom_apply.{c, v, r} (R := R), chart_homObjUnitInvApp_app_one.{c,
      v, r} (R := R)]
    rw [B.map_smul]
    exact mul_smul (show R.obj (op W.unop.left) from x)
      (R.map W.unop.hom.op _) (show B.obj (op W.unop.left) from B.map W.unop.hom.op y)
  rw [heq]
  infer_instance

end PresheafOfModules

namespace CategoryTheory
open MonoidalCategory
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor homComplexπ
  SheafOfModules.tensorObjIsoSheafification
  ringedSiteOrdinaryEvaluation ringedSiteOrdinaryBidual

noncomputable section Private

private local instance spSheafRestrictedSMul
    {D : Type c} [Category.{v} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    {S : Sheaf K CommRingCat.{r}}
    (M : SheafOfModules.{r} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (U : Dᵒᵖ) (W : (Over U.unop)ᵒᵖ) :
    SMul (((PresheafOfModules.restrictOver S.obj U.unop).obj
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)).val).obj W)
      ((ModuleCat.restrictScalars
        (((sheafCompose K (forget₂ CommRingCat RingCat)).obj S).obj.map W.unop.hom.op).hom).obj
          (M.val.obj (op W.unop.left))) :=
  (M.val.obj (op W.unop.left)).isModule.toSMul

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Name the category and its canonical structures so instance inference need not
rebuild the sheaf-category constructions in each finite-retract calculation. -/
@[implicit_reducible, no_expose] private def StrictPerfectModules :=
  SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)

set_option hygiene false in
local notation "𝓜" => StrictPerfectModules.{c, v, r} J R

private local instance spCategory : Category.{max c v r} 𝓜 :=
  inferInstanceAs (Category.{max c v r} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
private local instance spPreadditive : Preadditive 𝓜 :=
  inferInstanceAs (Preadditive (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
private local instance spAbelian : Abelian 𝓜 := inferInstanceAs (Abelian (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
private local instance spLimits : HasLimitsOfSize.{max c v r, max c v r} 𝓜 :=
  inferInstanceAs (HasLimitsOfSize.{max c v r, max c v r} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
private local instance spColimits : HasColimitsOfSize.{max c v r, max c v r} 𝓜 :=
  inferInstanceAs (HasColimitsOfSize.{max c v r, max c v r} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
private local instance spFiniteBiproducts : HasFiniteBiproducts 𝓜 :=
  HasFiniteBiproducts.of_hasFiniteProducts
private local instance spMonoidal : MonoidalCategory 𝓜 :=
  SheafOfModules.monoidalCategory R
private local instance spSymmetric : SymmetricCategory 𝓜 :=
  SheafOfModules.symmetricCategory R
private local instance spMonoidalPreadditive : MonoidalPreadditive 𝓜 :=
  SheafOfModules.cochainModulesPreadditive R

private theorem hom_flip_additive
    (B : 𝓜) :
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj B).Additive where
  map_add {X Y} f g := by
    exact SheafOfModules.hom_ext
      (PresheafOfModules.homObjMap_add_left f.unop.val g.unop.val (𝟙 B.val))

private theorem dual_bounded
    (E : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((homComplex.{c, v, max c v r, max c v r} (R := R) E
        (ringedSiteDualityUnitComplex.{c, v, r} J R)).X n) := by
  obtain ⟨a, b, hab⟩ := hE
  obtain ⟨α, γ, δ, β, hα, hγ, hd, hdd, hbound, _⟩ :=
    RingedSiteBoundedDual.boundedDualComponents.{c, v, r} R E a b hab
  exact ⟨-b, -a, hbound⟩

private noncomputable def homUnitIso
    (B : 𝓜) :
    SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) B ≅ B :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.chart_homObjUnitIso.{c, v, r} (R := R.obj) B.val)

@[irreducible]
private noncomputable def homPowerUnitIso (N : ℕ) :
    SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R)
      (∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
        (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≅
      ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) := by
  let O : 𝓜 := SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let H : 𝓜ᵒᵖ ⥤ 𝓜 :=
    (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj O
  let : H.Additive := hom_flip_additive.{c, v, r} J R O
  let : HasFiniteBiproducts 𝓜 := HasFiniteBiproducts.of_hasFiniteProducts
  let : HasBiproduct (C := 𝓜) (fun _ : Fin N ↦ H.obj (op O)) :=
    HasBiproductsOfShape.has_biproduct _
  exact H.mapIso (biproduct.isoProduct (C := 𝓜) (fun _ : Fin N ↦ O)).op ≪≫
    H.opMapBiproductIso (fun _ : Fin N ↦ O) ≪≫
    biproduct.mapIso (C := 𝓜) (fun _ ↦ homUnitIso.{c, v, r} J R O) ≪≫
    biproduct.isoProduct (C := 𝓜) _

private theorem dualTerm_isIso
    (E : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) (n : ℤ) :
    IsIso (RingedSiteBoundedDual.component.{c, v, r} R E (-n) n (neg_add_cancel n)) := by
  obtain ⟨a, b, hab⟩ := hE
  obtain ⟨α, γ, δ, β, hα, _⟩ :=
    RingedSiteBoundedDual.boundedDualComponents.{c, v, r} R E a b hab
  rw [← hα]
  infer_instance

private noncomputable def dualTermIso
    (E : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (n : ℤ) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)).X n ≅
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X (-n))
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) := by
  have := dualTerm_isIso.{c, v, r} J R E hE n
  exact asIso (RingedSiteBoundedDual.component.{c, v, r} R E (-n) n (neg_add_cancel n))

private theorem dual_package
    (E : CochainComplex (𝓜) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J
        R))) := by
  let O := SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let H : 𝓜ᵒᵖ ⥤ 𝓜 :=
    (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj O
  let e (n : ℤ) := dualTermIso.{c, v, r} J R E hE n
  let t (n : ℤ) := homPowerUnitIso.{c, v, r} J R (pE.N (-n))
  let s (n : ℤ) := (Retract.ofIso (e n)).trans
    (((Retract.mk (pE.i (-n)) (pE.p (-n)) (pE.splitting (-n))).op.map H).trans
      (Retract.ofIso (t n)))
  exact ⟨{ N := fun n ↦ pE.N (-n)
           i := fun n ↦ (s n).i
           p := fun n ↦ (s n).r
           splitting := fun n ↦ (s n).retract }⟩

private noncomputable def finitePowerFreeIso (N : ℕ) :
    (∏ᶜ fun _ : Fin N ↦ (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) : 𝓜)) ≅
      SheafOfModules.free (R := (sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
        (ULift.{max c v r} (Fin N)) := by
  let O : 𝓜 := SheafOfModules.unit _
  change (∏ᶜ fun _ : Fin N ↦ O) ≅ (∐ fun _ : ULift.{max c v r} (Fin N) ↦ O)
  exact (biproduct.isoProduct (fun _ : Fin N ↦ (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) : 𝓜))).symm ≪≫
    biproduct.whiskerEquiv (f := fun _ : Fin N ↦ O)
      (g := fun _ : ULift.{max c v r} (Fin N) ↦ O)
      (Equiv.ulift.{max c v r, 0} (α := Fin N)).symm (fun _ ↦ Iso.refl O) ≪≫
        biproduct.isoCoproduct (fun _ : ULift.{max c v r} (Fin N) ↦ O)

@[irreducible]
private noncomputable def dualProjectionUnit (E : CochainComplex 𝓜 ℤ)
    (n p : ℤ) (h : p + n = 0) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)).X n ⟶
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (E.X p)
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
  homComplexπ.{c, v, max c v r, max c v r} (R := R) E
    (ringedSiteDualityUnitComplex.{c, v, r} J R) n p 0 h ≫
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (𝟙 (E.X p))
        (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
              R) : 𝓜)).hom

private lemma dualProjectionUnit_apply (E : CochainComplex 𝓜 ℤ)
    (n p : ℤ) (h : p + n = 0) (U : Cᵒᵖ)
    (ξ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X p).val.obj (op W.unop.left)) :
    (((dualProjectionUnit.{c, v, r} J R E n p h).val.app U ξ).app W).hom x =
      (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E
        (ringedSiteDualityUnitComplex.{c, v, r} J R) n p 0 h).val.app U ξ).app W).hom x := by
  with_unfolding_all rfl

private theorem ordinaryBidual_isIso
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    IsIso (ringedSiteOrdinaryBidual.{c, v, r, w} J R E) := by
  obtain ⟨a, b, hab⟩ := hE
  obtain ⟨α, γ, δ, β, hα, hγ, hd, hdd, hbound, hδ, hβ, hfactor⟩ :=
    RingedSiteBoundedDual.boundedDualComponents.{c, v, r} R E a b hab
  have hδiso (n : ℤ) : IsIso (δ n) := by
    let e := finitePowerFreeIso.{c, v, r} J R (pE.N n)
    have h := SheafOfModules.ringedSite_finite_retract_dual_exact.{c, v, r}
      (R := R) (pE.N n) (E.X n) (pE.i n ≫ e.hom) (e.inv ≫ pE.p n)
      (by simpa [Category.assoc] using pE.splitting n)
    rcases h with ⟨_, _, _, _, ⟨d, hd, _⟩, _⟩
    have heq : δ n = d.hom := by
      apply SheafOfModules.hom_ext
      ext U : 2
      apply LinearMap.ext
      intro x
      apply PresheafOfModules.hom_ext
      intro W
      ext φ
      exact (hδ n U x W φ).trans (hd U x W φ).symm
    rw [heq]
    infer_instance
  have hβiso (n : ℤ) : IsIso (β.f n) := by
    have : IsIso (β.f n ≫ (γ n).hom) := by
      rw [hfactor]
      exact (n.negOnePow • asIso (δ n)).isIso_hom
    exact IsIso.of_isIso_comp_right _ (γ n).hom
  have hf : RingedSiteBidualFormula.{c, v, r} J R E β := by
    intro i q h h' U x W φ
    have hval := hβ i q 0 h h' U x W φ
    simp only [WeilConjectures.coefficientHomComponent_eq_homComplexπ]
    dsimp only [RingedSiteBoundedDual.complexDual, RingedSiteBoundedDual.zeroComplex,
      RingedSiteBoundedDual.coefficient, CochainComplex.singleFunctor,
      CochainComplex.singleFunctors, ringedSiteDualityUnitComplex] at hval ⊢
    exact hval
  have heq : ringedSiteOrdinaryBidual.{c, v, r, w} J R E = β := by
    unfold ringedSiteOrdinaryBidual
    exact (ringedSiteOrdinaryBidual_existsUnique.{c, v, r, w} J R E).unique
      (ringedSiteOrdinaryBidual_existsUnique.{c, v, r, w} J R E).exists.choose_spec hf
  rw [heq]
  exact HomologicalComplex.Hom.isIso_of_components _

open MonoidalCategory in
@[irreducible]
private noncomputable def tensorPure (A B : 𝓜) :
    A.val ⊗ B.val ⟶ (A ⊗ B).val :=
  (PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)).unit.app
      (A.val ⊗ B.val) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) A B).inv.val

open MonoidalCategory in
@[irreducible]
private noncomputable def tensorLift (A B T : 𝓜) (f : A.val ⊗ B.val ⟶ T.val) :
    A ⊗ B ⟶ T :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
    ((PresheafOfModules.sheafificationAdjunction.{max c v r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).obj)).homEquiv _ T).symm f

open MonoidalCategory in
private lemma tensorPure_lift (A B T : 𝓜) (f : A.val ⊗ B.val ⟶ T.val) :
    tensorPure.{c, v, r} J R A B ≫ (tensorLift.{c, v, r} J R A B T f).val = f := by
  with_unfolding_all
    let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
    have h := (adj.homEquiv (A.val ⊗ B.val) T).apply_symm_apply f
    rw [Adjunction.homEquiv_unit] at h
    change adj.unit.app (A.val ⊗ B.val) ≫ ((adj.homEquiv _ T).symm f).val = f at h
    unfold tensorPure tensorLift
    erw [Category.assoc, ← SheafOfModules.comp_val, Iso.inv_hom_id_assoc]
    exact h

open MonoidalCategory in
private lemma tensor_hom_ext (A B T : 𝓜) (f g : A ⊗ B ⟶ T)
    (h : ∀ U (x : A.val.obj U) (y : B.val.obj U),
      f.val.app U ((tensorPure.{c, v, r} J R A B).app U
        (x ⊗ₜ[R.obj.obj U] y)) =
      g.val.app U ((tensorPure.{c, v, r} J R A B).app U
        (x ⊗ₜ[R.obj.obj U] y))) : f = g := by
  let e := SheafOfModules.tensorObjIsoSheafification (R := R) A B
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R).obj)
  apply (cancel_epi e.inv).1
  apply (adj.homEquiv (A.val ⊗ B.val) T).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  unfold tensorPure at h
  exact h U x y

open MonoidalCategory in
private lemma tensorPure_whiskerLeft (A : 𝓜) {B B' : 𝓜} (f : B ⟶ B') :
    tensorPure.{c, v, r} J R A B ≫ (A ◁ f).val =
      (A.val ◁ f.val) ≫ tensorPure.{c, v, r} J R A B' := by
  with_unfolding_all
    have h := SheafOfModules.CochainScalarConstruction.pureMap_natural R (𝟙 A) f
    change tensorPure.{c, v, r} J R A B ≫ ((𝟙 A) ⊗ₘ f).val =
      ((𝟙 A.val) ⊗ₘ f.val) ≫ tensorPure.{c, v, r} J R A B' at h
    rw [id_tensorHom, id_tensorHom] at h
    exact h

@[irreducible]
private noncomputable def moduleScalarEvaluation (A B : 𝓜) :
    B ⊗ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⟶
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B :=
  tensorLift.{c, v, r} J R _ _ _
    (PresheafOfModules.sp_scalarEvaluation.{c, v, r} (R := R.obj) A.val B.val)

private lemma moduleScalarEvaluation_apply (A B : 𝓜) (U : Cᵒᵖ)
    (y : B.val.obj U)
    (φ : (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : A.val.obj (op W.unop.left)) :
    ((((moduleScalarEvaluation.{c, v, r} J R A B).val.app U)
      ((tensorPure.{c, v, r} J R B _).app U (y ⊗ₜ[R.obj.obj U] φ))).app W).hom x =
        (φ.app W).hom x • B.val.map W.unop.hom.op y := by
  with_unfolding_all
    let H := SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    have h := tensorPure_lift.{c, v, r} J R B H
      (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B)
      (PresheafOfModules.sp_scalarEvaluation.{c, v, r} (R := R.obj) A.val B.val)
    have h' := congrArg
      (fun (f : B.val ⊗ H.val ⟶
        (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B).val) ↦
          ((f.app U (y ⊗ₜ[R.obj.obj U] φ)).app W).hom x) h
    exact h'.trans (PresheafOfModules.sp_scalarEvaluation_apply.{c, v, r}
      (R := R.obj) A.val B.val U y φ W x)

open MonoidalCategory in
private lemma moduleScalarEvaluation_naturality (B : 𝓜) {A A' : 𝓜} (f : A' ⟶ A) :
    B ◁ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f (𝟙 (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≫
        moduleScalarEvaluation.{c, v, r} J R A' B =
      moduleScalarEvaluation.{c, v, r} J R A B ≫ SheafOfModules.homObjMap.{max c v r, v, c, max c v
        r} f (𝟙 B) := by
  with_unfolding_all
    apply tensor_hom_ext.{c, v, r} J R
    intro U y φ
    have hp := congrArg (fun k ↦ k.app U (y ⊗ₜ[R.obj.obj U] φ))
      (tensorPure_whiskerLeft.{c, v, r} J R B
        (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) f (𝟙 (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))))
    simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply] at hp
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change (((moduleScalarEvaluation.{c, v, r} J R A' B).val.app U
      (((B ◁ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} f (𝟙 (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))).val.app U)
        ((tensorPure.{c, v, r} J R B _).app U (y ⊗ₜ[R.obj.obj U] φ)))).app W).hom x = _
    erw [hp]
    exact (moduleScalarEvaluation_apply.{c, v, r} J R A' B U y _ W x).trans
      (moduleScalarEvaluation_apply.{c, v, r} J R A B U y φ W
        ((f.val.app (op W.unop.left)).hom x)).symm

private theorem tensorLift_isIso (A B T : 𝓜) (f : A.val ⊗ B.val ⟶ T.val)
    [IsIso f] : IsIso (tensorLift.{c, v, r} J R A B T f) := by
  with_unfolding_all
    let adj := PresheafOfModules.sheafificationAdjunction.{max c v r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
    have hc : IsIso (adj.counit.app T) := inferInstance
    have hm : IsIso ((PresheafOfModules.sheafification.{max c v r}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
        R).obj)).map f) := inferInstance
    unfold tensorLift
    rw [Adjunction.homEquiv_counit]
    exact (inferInstance : IsIso
      ((SheafOfModules.tensorObjIsoSheafification (R := R) A B).hom ≫
        ((PresheafOfModules.sheafification.{max c v r}
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj
            R).obj)).map f ≫ adj.counit.app T)))

private theorem moduleScalarEvaluation_unit_isIso (B : 𝓜) :
    IsIso (moduleScalarEvaluation.{c, v, r} J R (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) B) := by
  with_unfolding_all
    let O : 𝓜 := SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
    let T := SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) O B
    let f := PresheafOfModules.sp_scalarEvaluation.{c, v, r} (R := R.obj) O.val B.val
    have hf : IsIso f :=
      PresheafOfModules.sp_scalarEvaluation_unit_isIso.{c, v, r} (R := R.obj) B.val
    exact tensorLift_isIso.{c, v, r} J R B
      (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) O O) T f

private theorem iso_of_finite_basis
    {A : Type*} [Category A] [Preadditive A] {X Y U V : A}
    (f : X ⟶ Y) (g : U ⟶ V) [IsIso g] {I : Type*} [Fintype I]
    (a : I → (U ⟶ X)) (b : I → (X ⟶ U))
    (c : I → (V ⟶ Y)) (d : I → (Y ⟶ V))
    (hX : ∑ j, b j ≫ a j = 𝟙 X) (hY : ∑ j, d j ≫ c j = 𝟙 Y)
    (ha : ∀ j, a j ≫ f = g ≫ c j) (hb : ∀ j, f ≫ d j = b j ≫ g) : IsIso f := by
  classical
  let q := ∑ j, d j ≫ inv g ≫ a j
  refine ⟨⟨q, ?_, ?_⟩⟩
  · simp only [q, Preadditive.comp_sum, ← Category.assoc, hb]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hX
  · simp only [q, Preadditive.sum_comp, Category.assoc, ha, IsIso.inv_hom_id_assoc]
    exact hY

private theorem termEvaluation_isIso_of_retract
    (A B : 𝓜) (N : ℕ) (i : A ⟶ ∏ᶜ fun _ : Fin N ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (p : (∏ᶜ fun _ : Fin N ↦ (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) : 𝓜)) ⟶ A) (hip
        : i ≫ p = 𝟙 A) :
    IsIso (moduleScalarEvaluation.{c, v, r} J R A B) := by
  let O : 𝓜 := SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let H : 𝓜ᵒᵖ ⥤ 𝓜 :=
    (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj O
  let H' : 𝓜ᵒᵖ ⥤ 𝓜 := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj B
  let : H.Additive := hom_flip_additive.{c, v, r} J R O
  let : H'.Additive := hom_flip_additive.{c, v, r} J R B
  let : HasFiniteBiproducts 𝓜 := HasFiniteBiproducts.of_hasFiniteProducts
  let e := biproduct.isoProduct (C := 𝓜) (fun _ : Fin N ↦ O)
  let u (j : Fin N) := biproduct.ι (fun _ : Fin N ↦ O) j ≫ e.hom ≫ p
  let q (j : Fin N) := i ≫ e.inv ≫ biproduct.π (fun _ : Fin N ↦ O) j
  have h : ∑ j, q j ≫ u j = 𝟙 A := by
    simp only [q, u, Category.assoc, ← Preadditive.comp_sum]
    simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total]
    simp [hip]
  have hunit := moduleScalarEvaluation_unit_isIso.{c, v, r} J R B
  let K := H ⋙ tensorLeft B
  let : (tensorLeft B).Additive := by
    let : MonoidalPreadditive 𝓜 := SheafOfModules.cochainModulesPreadditive R
    exact tensorLeft_additive B
  let : K.Additive := inferInstance
  let ev := moduleScalarEvaluation.{c, v, r} J R A B
  apply iso_of_finite_basis (A := 𝓜) ev
    (moduleScalarEvaluation.{c, v, r} J R O B)
    (fun j ↦ K.map (q j).op) (fun j ↦ K.map (u j).op)
    (fun j ↦ H'.map (q j).op) (fun j ↦ H'.map (u j).op)
  · simp only [← K.map_comp, ← op_comp, ← K.map_sum, ← op_sum, h, op_id, K.map_id]
    rfl
  · simp only [← H'.map_comp, ← op_comp, ← H'.map_sum, ← op_sum, h, op_id, H'.map_id]
    rfl
  · intro j
    exact moduleScalarEvaluation_naturality.{c, v, r} J R B (q j)
  · intro j
    exact (moduleScalarEvaluation_naturality.{c, v, r} J R B (u j)).symm

section AssemblyProof
attribute [local semireducible] SheafOfModules.monoidalCategory
private theorem ordinaryEvaluation_isIso_assembly
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E F : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    IsIso (ringedSiteOrdinaryEvaluation.{c, v, r, w} J R E F) := by
  obtain ⟨a, b, hab⟩ := hE
  obtain ⟨θ, hθ, hassembly⟩ := RingedSiteBoundedEvaluation.assembly.{c, v, r} R E F a b hab
  have hθeq (i : ℤ) (B : 𝓜) :
      θ i B = moduleScalarEvaluation.{c, v, r} J R (E.X i) B := by
    apply tensor_hom_ext.{c, v, r} J R
    intro U y φ
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    with_unfolding_all
      have h₁ := hθ i B U y φ W x
      have h₂ := moduleScalarEvaluation_apply.{c, v, r} J R (E.X i) B U y φ W x
      dsimp only [RingedSiteBoundedEvaluation.pureTensor] at h₁
      unfold tensorPure at h₂ ⊢
      exact h₁.trans h₂.symm
  have hθiso (i : ℤ) (B : 𝓜) : IsIso (θ i B) := by
    rw [hθeq]
    exact termEvaluation_isIso_of_retract.{c, v, r} J R (E.X i) B
      (pE.N i) (pE.i i) (pE.p i) (pE.splitting i)
  obtain ⟨ε, δ, hδ, hpos, hneg, _⟩ := hassembly hθiso
  have hf : RingedSiteEvaluationFormula.{c, v, r} J R E F ε.hom := by
    constructor
    · intro p q n i hpq hiq hin U y φ W x
      subst p
      have h := hpos (i + n) q n i hpq hiq rfl U y φ W x
      have hρ := dualProjectionUnit_apply.{c, v, r} J R E q i hiq U φ W x
      simp only [WeilConjectures.coefficientHomComponent_eq_homComplexπ]
      with_unfolding_all
        exact h.trans (congrArg (fun z : R.obj.obj (op W.unop.left) ↦
          z • (show (F.X (i + n)).val.obj (op W.unop.left) from
            (F.X (i + n)).val.map W.unop.hom.op y)) hρ)
    · intro p q n i t hpq hit hiq U y φ
      have h := hneg p q n i t hpq hit hiq
      have h' := congrArg (fun k ↦ k.val.app U
        ((tensorPure.{c, v, r} J R (F.X p) _).app U (y ⊗ₜ[R.obj.obj U] φ))) h
      with_unfolding_all exact h'
  have heq : ringedSiteOrdinaryEvaluation.{c, v, r, w} J R E F = ε.hom := by
    unfold ringedSiteOrdinaryEvaluation
    exact ((ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r, w} J R E F).unique
      (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r, w} J R E F).exists.choose_spec hf)
  rw [heq]
  infer_instance

end AssemblyProof

private theorem term_exact
    (A : 𝓜) (N : ℕ)
    (i : A ⟶ ∏ᶜ fun _ : Fin N ↦ (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) : 𝓜))
    (p : (∏ᶜ fun _ : Fin N ↦ (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) : 𝓜)) ⟶ A) (hip : i ≫ p = 𝟙 A)
    (S : ShortComplex 𝓜) (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (𝟙 A) S.f ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (𝟙 A) S.f)
        (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (𝟙 A) S.g) hz).ShortExact := by
  let e := finitePowerFreeIso.{c, v, r} J R N
  have h := SheafOfModules.ringedSite_finite_retract_dual_exact.{c, v, r}
    (R := R) N A (i ≫ e.hom) (e.inv ≫ p) (by simpa [Category.assoc] using hip)
  rcases h with ⟨_, _, _, _, _, hexact, _⟩
  exact hexact S hS

private theorem homAugmentation_quasiIso
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex 𝓜 ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E)
    (F : CochainComplex 𝓜 ℤ) :
    QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F)) := by
  let : IsGrothendieckAbelian.{max c v r} 𝓜 :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let η := (ringedSiteHomAugmentation.{c, v, r} J R).app F
  have hη : QuasiIso η := by
    change QuasiIso ((CochainComplex.toKInjectiveResolution.{max c v r} 𝓜).app F)
    exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max c v r} 𝓜 F).2
  have h := SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms.{c, v, r}
    J R E hE (fun n S hS ↦ term_exact.{c, v, r} J R (E.X n)
      (pE.N n) (pE.i n) (pE.p n) (pE.splitting n) S hS) η
  simp only [ringedSiteHomComplexMap, op_id, Functor.map_id, NatTrans.id_app]
  erw [Category.id_comp]
  exact h

end Private

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- Ordinary duality for a bounded complex of finite-free retracts.
Source: Stacks Project, sites-cohomology.tex, Tags 08JH and 08JJ,
lemma-Rhom-strictly-perfect and the strictly perfect case of lemma-dual-perfect-complex.
(blueprint: lem-sfb-ringed-site-strict-perfect-hom).

Proof: split each term into a finite power of the coefficient sheaf. Dualizing
its inclusion and projection gives a splitting for its dual. The dual basis
identity gives mutually inverse termwise bidual and tensor-Hom evaluations.
The Hom functor of a term is a retract of a finite-power functor, hence exact.
The bounded-exact-term Hom lemma applied to the resolution augmentation gives
both ordinary-to-derived quasi-isomorphisms. The dual complex has term
(E^(-q))^dual in degree q, differential (-1)^(q+1) times the dual differential,
and bounds [-b,-a]. Its terms remain finite-free retracts. Under the Hom-product
projections, signed ordinary biduality is
(-1)^i times termwise biduality, hence invertible. For an arbitrary F the
ordinary evaluation in degree n is the finite direct sum over p+q=n of
F^p tensor (E^(-q))^dual to Hom(E^(-q),F^p). Each summand is invertible by
the dual basis identity. The two differentials are d_F f-(-1)^n f d_E,
so these degreewise inverses give an inverse chain map. The argument includes
zero ranks, the zero ring, odd shifts, and unbounded F. -/
theorem ringedSiteStrictPerfectHom
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n))
    (pE : SheafOfModules.StrictPerfectCoefficientPackageOnSite _ E) :
    let D := homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (D.X n)) ∧
    Nonempty (SheafOfModules.StrictPerfectCoefficientPackageOnSite _ D) ∧
    (∀ F, QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) ∧
    QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 D)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app
        (ringedSiteDualityUnitComplex.{c, v, r} J R))) ∧
    IsIso (ringedSiteOrdinaryBidual.{c, v, r} J R E) ∧
    (∀ F, IsIso (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F)) := by
  let D := homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
    r} J R)
  have hD := dual_bounded.{c, v, r} J R E hE
  obtain ⟨pD⟩ := dual_package.{c, v, r} J R E hE pE
  refine ⟨hD, ⟨pD⟩, homAugmentation_quasiIso.{c, v, r, w} J R E hE pE,
    homAugmentation_quasiIso.{c, v, r, w} J R D hD pD
      (ringedSiteDualityUnitComplex.{c, v, r} J R),
    ordinaryBidual_isIso.{c, v, r, w} J R E hE pE, ?_⟩
  intro F
  exact ordinaryEvaluation_isIso_assembly.{c, v, r, w} J R E F hE pE

end CategoryTheory
