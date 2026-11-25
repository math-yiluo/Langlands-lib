/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicIntrinsicCompletion
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulKFlat
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.Right.RightFractionDenseSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Koszul and quotient reconstruction over completed coefficients

The Koszul functor extends the recorded explicit fibre model on maps; it introduces
no second coefficient sheaf or Koszul complex. The quotient unit is independently
normalized on all K-flat representatives by the ordinary quotient maps.

## References

* Stacks Project, Tags 091N, 091Z, 099L and 099M
* Stacks Tag 00W1
* Stacks Tags 079B and 079Q
* Stacks Tag 0941
* Stacks Tags 06XN and 06YY
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

/-- Fix the additive coefficient universe when elaborating the recorded models. -/
local instance reconstructionAbSheafify (Y : Scheme.{t}) :
    HasSheafify (ProEt.topology Y) AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{t, 0} Y

/-- Use the canonical local-equivalence criterion in the same additive universe. -/
local instance reconstructionAbLocallyBijective (Y : Scheme.{t}) :
    (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} Y

/-- Fix the commutative-ring coefficient universe of the completed tensor structure. -/
local instance reconstructionRingSheafify (Y : Scheme.{t}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{t + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{t, 0} Y

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionTowersGrothendieckGeneric
    (B : Type*) [Category B] [Abelian B] [IsGrothendieckAbelian.{t + 1} B] :
    IsGrothendieckAbelian.{t + 1} (ℕᵒᵖ ⥤ B) := by
  let G := separator B
  have hG := isSeparator_separator B
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint B n).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight B n
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ B) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{t + 1, t + 1} (ℕᵒᵖ ⥤ B) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{t + 1, t + 1} (ℕᵒᵖ ⥤ B) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

/-- Strict towers of modules over the completed ring form a Grothendieck category. -/
theorem reconstructionTowers_grothendieck :
    IsGrothendieckAbelian.{t + 1} (CompletedAdicTowers T d) := by
  have : IsGrothendieckAbelian.{t + 1} (CompletedAdicModules T d) :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{t + 1, t, t + 1, 0}
      (ProEt.topology T) (completedAdicRing T d)
  exact reconstructionTowersGrothendieckGeneric (CompletedAdicModules T d)

attribute [instance] reconstructionTowers_grothendieck

/-- The actual ordinary strict inverse-limit functor. -/
abbrev reconstructionLimit : CompletedAdicTowers T d ⥤ CompletedAdicModules T d := lim

/-- Strict inverse limit is additive. -/
@[instance]
theorem reconstructionLimit_additive : (reconstructionLimit T d).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [reconstructionLimit, Preadditive.add_comp, Preadditive.comp_add]

/-- The total right derived strict inverse limit with its universal comparison. -/
abbrev reconstructionRlim : DerivedCategory (CompletedAdicTowers T d) ⥤
    DerivedCategory (CompletedAdicModules T d) := (reconstructionLimit T d).rightDerivedFunctor

/-- The universal derived-limit comparison on complexes of strict towers. -/
def reconstructionRlimComparison (P : CochainComplex (CompletedAdicTowers T d) ℤ) :
    DerivedCategory.Q.obj
        (((reconstructionLimit T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      (reconstructionRlim T d).obj (DerivedCategory.Q.obj P) :=
  (DerivedCategory.quotientCompQhIso _).inv.app
      (((reconstructionLimit T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
    DerivedCategory.Qh.map
      (((reconstructionLimit T d).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app P) ≫
    (reconstructionLimit T d).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
    (reconstructionRlim T d).map ((DerivedCategory.quotientCompQhIso _).hom.app P)

/-- The canonical quotient module map sends one to one on every section. -/
theorem reconstructionQuotientUnit_exists (n : ℕ) :
    ∃! u : SheafOfModules.unit (completedAdicRing T d) ⟶ completedAdicFiniteModule T d n,
      ∀ U : T.ProEtᵒᵖ,
        u.val.app U (1 : (completedAdicRing T d).obj.obj U) =
          (1 : (completedAdicFiniteRing T d n).obj.obj U) := by
  let M := completedAdicFiniteModule T d n
  let s : M.sections := M.val.sectionsMk
    (fun U ↦ (1 : (completedAdicFiniteRing T d n).obj.obj U)) (by
    intro U V f
    change (completedAdicFiniteRing T d n).obj.map f 1 = 1
    exact map_one _)
  refine ⟨M.unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)
  · intro u hu
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hu U).trans
      (congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)).symm

/-- The residue-normalized module map from A_T to its n+1-st quotient. -/
def reconstructionQuotientUnit (n : ℕ) :
    SheafOfModules.unit (completedAdicRing T d) ⟶ completedAdicFiniteModule T d n :=
  (reconstructionQuotientUnit_exists T d n).exists.choose

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionQuotientUnit_step (n : ℕ) :
    reconstructionQuotientUnit T d (n + 1) ≫ completedAdicFiniteModuleStep T d n =
      reconstructionQuotientUnit T d n := by
  apply (completedAdicFiniteModule T d n).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  change (completedAdicFiniteModuleStep T d n).val.app U
    ((reconstructionQuotientUnit T d (n + 1)).val.app U
      (1 : (completedAdicRing T d).obj.obj U)) =
      (reconstructionQuotientUnit T d n).val.app U
        (1 : (completedAdicRing T d).obj.obj U)
  rw [reconstructionQuotientUnit, reconstructionQuotientUnit,
    (reconstructionQuotientUnit_exists T d (n + 1)).exists.choose_spec U,
    (reconstructionQuotientUnit_exists T d n).exists.choose_spec U,
    completedAdicFiniteModuleStep,
    (completedAdicFiniteModuleStep_exists T d n).exists.choose_spec U]
  change (completedAdicFiniteStep T d n).hom.app U
    (1 : (completedAdicFiniteRing T d (n + 1)).obj.obj U) =
      (1 : (completedAdicFiniteRing T d n).obj.obj U)
  exact map_one _

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary completion unit is determined by all quotient tensor maps. -/
theorem reconstructionOrdinaryUnit_exists :
    ∃! η : 𝟭 (CompletedAdicModules T d) ⟶
        completedAdicOrdinaryTower T d ⋙ reconstructionLimit T d,
      ∀ (M : CompletedAdicModules T d) (n : ℕ),
        η.app M ≫ limit.π ((completedAdicOrdinaryTower T d).obj M) (op n) =
          (ρ_ M).inv ≫ (M ◁ reconstructionQuotientUnit T d n) := by
  let c (M : CompletedAdicModules T d) : Cone ((completedAdicOrdinaryTower T d).obj M) :=
    { pt := M
      π := NatTrans.ofOpSequence
        (fun n ↦ (ρ_ M).inv ≫ (M ◁ reconstructionQuotientUnit T d n)) (by
          intro n
          simp only [Functor.const_obj_map, completedAdicOrdinaryTower,
            Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
          change _ = ((ρ_ M).inv ≫ (M ◁ reconstructionQuotientUnit T d (n + 1))) ≫
            (M ◁ completedAdicFiniteModuleStep T d n)
          rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
            reconstructionQuotientUnit_step]
          exact Category.id_comp _) }
  let η : 𝟭 (CompletedAdicModules T d) ⟶
      completedAdicOrdinaryTower T d ⋙ reconstructionLimit T d :=
    { app := fun M ↦ limit.lift _ (c M)
      naturality := by
        intro M N h
        apply limit.hom_ext
        intro n
        simp only [Functor.id_map, Functor.comp_map, reconstructionLimit,
          ← limMap_eq, Category.assoc, limMap_π, limit.lift_π, limit.lift_π_assoc]
        change h ≫ (ρ_ N).inv ≫ (N ◁ reconstructionQuotientUnit T d n.unop) =
          ((ρ_ M).inv ≫ (M ◁ reconstructionQuotientUnit T d n.unop)) ≫
            (h ▷ completedAdicFiniteModule T d n.unop)
        rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc]
        change (ρ_ M).inv ≫
            (h ▷ SheafOfModules.unit (completedAdicRing T d)) ≫
              (N ◁ reconstructionQuotientUnit T d n.unop) = _
        simpa only [Category.assoc] using congrArg (fun z ↦ (ρ_ M).inv ≫ z)
          (whisker_exchange h (reconstructionQuotientUnit T d n.unop)).symm }
  refine ⟨η, ?_, ?_⟩
  · intro M n
    exact limit.lift_π (c M) (op n)
  · intro θ hθ
    apply NatTrans.ext
    funext M
    apply limit.hom_ext
    intro n
    exact (hθ M n.unop).trans (limit.lift_π (c M) n).symm

/-- The map to the ordinary limit induced by the actual quotient maps. -/
def reconstructionOrdinaryUnit : 𝟭 (CompletedAdicModules T d) ⟶
    completedAdicOrdinaryTower T d ⋙ reconstructionLimit T d :=
  (reconstructionOrdinaryUnit_exists T d).exists.choose

/-- The same reduction counit on a complex representative, with localization factors. -/
def reconstructionReductionComplexCounit (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    (completedAdicReduction T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  (completedAdicReductionData T d).complexCounit P

/-- The strict reduction counit is invertible on every unbounded K-flat model. -/
theorem reconstructionTowerCounit_isIso
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    IsIso (reconstructionReductionComplexCounit T d P) := by
  exact (completedAdicReductionData T d).complexCounit_isIso P hP

/-- The quotient completion unit on one K-flat representative at every tower level. -/
def reconstructionUnitOnKFlat (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P) :
    DerivedCategory.Q.obj P ⟶
      (reconstructionRlim T d).obj ((completedAdicReduction T d).obj (DerivedCategory.Q.obj P)) :=
  derivedCompletionModelUnit (completedAdicReductionData T d) (reconstructionLimit T d)
    (reconstructionRlim T d) (reconstructionLimit T d).rightDerivedFunctorUnit
    (reconstructionOrdinaryUnit T d) P hP

section ModelUnit

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive] (L : C ⥤ B) [L.Additive]
  (LF : DerivedCategory B ⥤ DerivedCategory C)
  (RF : DerivedCategory C ⥤ DerivedCategory B)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (u : 𝟭 B ⟶ F ⋙ L)

private abbrev reconstructionModelCounit (P : CochainComplex B ℤ) :=
  LF.map ((DerivedCategory.quotientCompQhIso B).inv.app P) ≫
  ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) ≫
  DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
  (DerivedCategory.quotientCompQhIso C).hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

private abbrev reconstructionModelLimit (P : CochainComplex C ℤ) :=
  (DerivedCategory.quotientCompQhIso B).inv.app
      ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
  DerivedCategory.Qh.map ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
  δ.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
  RF.map ((DerivedCategory.quotientCompQhIso C).hom.app P)

private abbrev reconstructionModelAlpha : DerivedCategory.Qh ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ RF :=
  (Functor.leftUnitor DerivedCategory.Qh).inv ≫
  Functor.whiskerRight (Functor.mapHomotopyCategoryIdIso B (.up ℤ)).inv DerivedCategory.Qh ≫
  Functor.whiskerRight (NatTrans.mapHomotopyCategory u (.up ℤ)) DerivedCategory.Qh ≫
  Functor.whiskerRight
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).inv DerivedCategory.Qh ≫
  (Functor.associator (F.mapHomotopyCategory (.up ℤ))
    (L.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).hom ≫
  Functor.whiskerLeft (F.mapHomotopyCategory (.up ℤ)) δ

private abbrev reconstructionModelGamma : DerivedCategory.Qh ⋙ (LF ⋙ RF) ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ RF :=
  (Functor.associator DerivedCategory.Qh LF RF).inv ≫
  Functor.whiskerRight ε RF ≫
  (Functor.associator (F.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh RF).hom

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionModelUnit_normalization (P : CochainComplex B ℤ)
    [IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))] :
    let X := (HomotopyCategory.quotient B (.up ℤ)).obj P
    let e := reconstructionModelCounit F LF ε P
    let g := reconstructionModelGamma F LF RF ε
    ∀ (he : IsIso e) (hg : IsIso (g.app X)),
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) ≫
        reconstructionModelLimit L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        RF.map (@inv _ _ _ _ e he) =
      (reconstructionModelAlpha F L RF δ u).app X ≫ @inv _ _ _ _ (g.app X) hg := by
  intro X e g he hg
  have hid : (Functor.mapHomotopyCategoryIdIso B (.up ℤ)).inv.app X = 𝟙 _ := by
    apply (cancel_mono ((Functor.mapHomotopyCategoryIdIso B (.up ℤ)).hom.app X)).1
    rw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id,
      Category.id_comp]
    rfl
  have hcomp : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).inv.app X =
      𝟙 _ := by
    apply (cancel_mono
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ L)) (.up ℤ)).hom.app X)).1
    rw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
      Category.id_comp]
    rfl
  have hred : e = ε.app X := by
    dsimp only [e, reconstructionModelCounit]
    change LF.map (𝟙 _) ≫ ε.app X ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact Category.comp_id _
  have hlim : reconstructionModelLimit L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      δ.app ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
    dsimp only [reconstructionModelLimit]
    change 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ RF.map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    rfl
  have ha : (reconstructionModelAlpha F L RF δ u).app X =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) ≫
        δ.app ((F.mapHomotopyCategory (.up ℤ)).obj X) := by
    dsimp only [reconstructionModelAlpha, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app]
    rw [hid, hcomp]
    change 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫ _ = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hg' : g.app X = RF.map (ε.app X) := by
    change 𝟙 _ ≫ RF.map (ε.app X) ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  have hf : DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) ≫
        reconstructionModelLimit L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (reconstructionModelAlpha F L RF δ u).app X := by
    exact (congrArg (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) ≫ ·) hlim).trans ha.symm
  have hm : RF.map e = g.app X := (congrArg RF.map hred).trans hg'.symm
  have hi : RF.map (inv e) = inv (g.app X) := by
    apply (cancel_mono (g.app X)).1
    calc
      _ = RF.map (inv e) ≫ RF.map e := congrArg (RF.map (inv e) ≫ ·) hm.symm
      _ = 𝟙 _ := by rw [← RF.map_comp, IsIso.inv_hom_id, RF.map_id]
      _ = _ := (IsIso.inv_hom_id (g.app X)).symm
  exact (Category.assoc _ _ _).symm.trans (congrArg₂ (fun f g ↦ f ≫ g) hf hi)

end ModelUnit

set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionRestrictionLocalization
    {A : Type*} [Category A] {D : Type*} [Category D]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ D) [L.IsLocalization W] (P : ObjectProperty A)
    (res : ∀ X : A, ∃ (Y : P.FullSubcategory) (s : Y.obj ⟶ X), W s) :
    (P.ι ⋙ L).IsLocalization (W.inverseImage P.ι) := by
  let V := W.inverseImage P.ι
  obtain ⟨_, F, hF, ⟨e⟩⟩ :=
    rightFractionDenseSubcategory W inferInstance P res L V.Q
  have : F.IsEquivalence := hF
  have : (V.Q ⋙ F).IsLocalization V := inferInstance
  exact Functor.IsLocalization.of_iso V e

private theorem reconstructionDescendUnit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : ObjectProperty C) (L : C ⥤ D) (W : MorphismProperty C)
    [(P.ι ⋙ L).IsLocalization (W.inverseImage P.ι)]
    (F G : D ⥤ E) (R : C ⥤ E) (α : L ⋙ F ⟶ R) (γ : L ⋙ G ⟶ R)
    (hγ : ∀ X : P.FullSubcategory, IsIso (γ.app X.obj)) :
    ∃! η : F ⟶ G, ∀ X : P.FullSubcategory,
      η.app (L.obj X.obj) = α.app X.obj ≫ inv (γ.app X.obj) := by
  let S := P.ι ⋙ L
  let V := W.inverseImage P.ι
  let τ : S ⋙ F ⟶ S ⋙ G :=
    { app := fun X ↦ α.app X.obj ≫ inv (γ.app X.obj)
      naturality := by
        intro X Y f
        change (L ⋙ F).map f.hom ≫ α.app Y.obj ≫ inv (γ.app Y.obj) =
          (α.app X.obj ≫ inv (γ.app X.obj)) ≫ (L ⋙ G).map f.hom
        rw [← Category.assoc, α.naturality, Category.assoc, Category.assoc]
        apply congrArg (α.app X.obj ≫ ·)
        apply (cancel_mono (γ.app Y.obj)).1
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rw [γ.naturality f.hom]
        simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  let E' := (Functor.whiskeringLeft P.FullSubcategory D E).obj S
  have : E'.Full := Localization.full_whiskeringLeft S V E
  refine ⟨E'.preimage τ, ?_, ?_⟩
  · intro X
    exact congrArg (fun k ↦ k.app X) (E'.map_preimage τ)
  · intro θ hθ
    apply Localization.natTrans_ext S V
    intro X
    exact (hθ X).trans (congrArg (fun k ↦ k.app X) (E'.map_preimage τ)).symm

section DerivedUnit

variable {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (F : B ⥤ C) [F.Additive] (L : C ⥤ B) [L.Additive]
  (LF : DerivedCategory B ⥤ DerivedCategory C)
  (RF : DerivedCategory C ⥤ DerivedCategory B)
  (ε : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (u : 𝟭 B ⟶ F ⋙ L)
  (P : ObjectProperty (HomotopyCategory B (.up ℤ)))
  (hP : (P.ι ⋙ DerivedCategory.Qh).IsLocalization
    ((HomotopyCategory.quasiIso B (.up ℤ)).inverseImage P.ι))
  (hε : ∀ X : P.FullSubcategory, IsIso (ε.app X.obj))

include hP hε

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionModelUnit_exists :
    ∃! η : 𝟭 (DerivedCategory B) ⟶ LF ⋙ RF,
      ∀ (K : CochainComplex B ℤ) (_hK : P ((HomotopyCategory.quotient B (.up ℤ)).obj K)),
        ∀ he : IsIso (reconstructionModelCounit F LF ε K),
          η.app (DerivedCategory.Q.obj K) =
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app K) ≫
              reconstructionModelLimit L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
                RF.map (@inv _ _ _ _ (reconstructionModelCounit F LF ε K) he) := by
  have := hP
  let α := reconstructionModelAlpha F L RF δ u
  let γ := reconstructionModelGamma F LF RF ε
  have hγ (X : P.FullSubcategory) : IsIso (γ.app X.obj) := by
    have := hε X
    dsimp only [γ, reconstructionModelGamma, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app]
    infer_instance
  obtain ⟨η, hη, hu⟩ := reconstructionDescendUnit P DerivedCategory.Qh
    (HomotopyCategory.quasiIso B (.up ℤ))
    (𝟭 (DerivedCategory B)) (LF ⋙ RF)
    (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙ RF) α γ hγ
  have hn (K : CochainComplex B ℤ)
      (hK : P ((HomotopyCategory.quotient B (.up ℤ)).obj K))
      (he : IsIso (reconstructionModelCounit F LF ε K)) :
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app K) ≫
        reconstructionModelLimit L RF δ ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          RF.map (@inv _ _ _ _ (reconstructionModelCounit F LF ε K) he) =
        α.app ((HomotopyCategory.quotient B (.up ℤ)).obj K) ≫
          @inv _ _ _ _ (γ.app ((HomotopyCategory.quotient B (.up ℤ)).obj K))
            (hγ ⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, hK⟩) := by
    have := hε ⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, hK⟩
    exact reconstructionModelUnit_normalization F L LF RF ε δ u K he
      (hγ ⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, hK⟩)
  refine ⟨η, ?_, ?_⟩
  · intro K hK he
    exact (hη ⟨(HomotopyCategory.quotient B (.up ℤ)).obj K, hK⟩).trans (hn K hK he).symm
  · intro θ hθ
    apply hu θ
    intro X
    have hX : IsIso (reconstructionModelCounit F LF ε X.obj.as) := by
      let : IsIso (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj X.obj.as)) := hε X
      dsimp only [reconstructionModelCounit]
      infer_instance
    exact (hθ X.obj.as X.property hX).trans (hn X.obj.as X.property hX)

end DerivedUnit

set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionDerivedUnit_exists
    {B C : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    {F : B ⥤ C} [F.Additive] {E : CochainComplex B ℤ → Prop}
    (D : DerivedReductionModelData F E)
    (L : C ⥤ B) [L.Additive] (RF : DerivedCategory C ⥤ DerivedCategory B)
    (δ : L.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    (u : 𝟭 B ⟶ F ⋙ L)
    (hS : ((ObjectProperty.ι (fun X : HomotopyCategory B (.up ℤ) ↦ E X.as)) ⋙
      DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso B (.up ℤ)).inverseImage
        (ObjectProperty.ι (fun X : HomotopyCategory B (.up ℤ) ↦ E X.as)))) :
    ∃! η : 𝟭 (DerivedCategory B) ⟶ D.reduction ⋙ RF,
      ∀ (K : CochainComplex B ℤ) (hK : E K),
        η.app (DerivedCategory.Q.obj K) = derivedCompletionModelUnit D L RF δ u K hK := by
  let P : ObjectProperty (HomotopyCategory B (.up ℤ)) := fun X ↦ E X.as
  have hε (X : P.FullSubcategory) : IsIso (D.counit.app X.obj) :=
    D.isIso_counit X.obj.as X.property
  obtain ⟨η, hη, hu⟩ := reconstructionModelUnit_exists F L D.reduction RF D.counit δ u P hS hε
  refine ⟨η, ?_, ?_⟩
  · intro K hK
    exact hη K hK (D.complexCounit_isIso K hK)
  · intro θ hθ
    apply hu θ
    intro K hK he
    exact hθ K hK

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived quotient unit is fixed by its value on all K-flat models. -/
theorem reconstructionCompletionUnit_exists :
    ∃! η : 𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
        completedAdicReduction T d ⋙ reconstructionRlim T d,
      ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ)
        (hP : CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P),
        η.app (DerivedCategory.Q.obj P) = reconstructionUnitOnKFlat T d P hP := by
  classical
  let B := CompletedAdicModules T d
  let F := completedAdicOrdinaryTower T d
  let L := reconstructionLimit T d
  let RF := reconstructionRlim T d
  let LF := completedAdicReduction T d
  let Qh := DerivedCategory.Qh (C := B)
  let H := HomotopyCategory B (ComplexShape.up ℤ)
  let HF := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let P : ObjectProperty H := fun X ↦
    CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) X.as
  let W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
  let V := W.inverseImage P.ι
  let S := P.ι ⋙ Qh
  have hS : S.IsLocalization V := by
    apply reconstructionRestrictionLocalization W Qh P
    intro X
    obtain ⟨K, f, hK, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedAdicCommRing T d) X.as
    exact ⟨⟨(HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj K, hK⟩,
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map f,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩
  exact reconstructionDerivedUnit_exists (completedAdicReductionData T d) L RF
    L.rightDerivedFunctorUnit (reconstructionOrdinaryUnit T d) hS

/-- The map comp_K induced by quotient maps, independently of chosen resolutions. -/
def reconstructionCompletionUnit : 𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
    completedAdicReduction T d ⋙ reconstructionRlim T d :=
  (reconstructionCompletionUnit_exists T d).exists.choose

/-- Tensoring a map of representatives and taking products gives the canonical product map. -/
def reconstructionKoszulProductMap (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    completedAdicKoszulProduct T d r a C ⟶ completedAdicKoszulProduct T d r a D :=
  letI := SheafOfModules.monoidalCategory (completedAdicCommRing T d)
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  Limits.Pi.map (fun m ↦ HomologicalComplex.mapBifunctorMap h
    (𝟙 (completedAdicKoszul T d r a m)) (curriedTensor _) (ComplexShape.up ℤ))

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
private theorem reconstructionTensorSquare
    {B : Type*} [Category B] [Abelian B] [HasCountableCoproducts B]
    (F : B ⥤ B ⥤ B) [F.PreservesZeroMorphisms]
    [∀ X : B, (F.obj X).PreservesZeroMorphisms]
    {C D X Y : CochainComplex B ℤ} (h : C ⟶ D) (t : X ⟶ Y) :
    HomologicalComplex.mapBifunctorMap h (𝟙 X) F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 D) t F (.up ℤ) =
      HomologicalComplex.mapBifunctorMap (𝟙 C) t F (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap h (𝟙 Y) F (.up ℤ) := by
  exact ((F.map₂CochainComplex.map h).naturality t).symm

set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
/-- Product maps commute with the actual one-minus-transition endomorphism. -/
theorem reconstructionKoszulProductMap_comm (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    reconstructionKoszulProductMap T d r a h ≫ (-completedAdicKoszulOneSubShift T d r a D) =
      (-completedAdicKoszulOneSubShift T d r a C) ≫
        reconstructionKoszulProductMap T d r a h := by
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, neg_inj]
  change Limits.Pi.map (fun m ↦ HomologicalComplex.mapBifunctorMap h
      (𝟙 (completedAdicKoszul T d r a m)) (curriedTensor _) (.up ℤ)) ≫
      towerTransitionEndomorphism (completedAdicKoszulTensorStep T d r a D) =
    towerTransitionEndomorphism (completedAdicKoszulTensorStep T d r a C) ≫ _
  apply towerTransitionEndomorphism_natural_backward
  intro m
  exact reconstructionTensorSquare (curriedTensor _) h
    (completedAdicKoszulStep T d r a m)

/-- The canonical map of the recorded Koszul fibres, using the map of mapping cones. -/
def reconstructionKoszulFiberMap (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    completedAdicKoszulFibre T d r a C ⟶ completedAdicKoszulFibre T d r a D :=
  (HomologicalComplex.homotopyCofiber.mapArrowHom
    (-completedAdicKoszulOneSubShift T d r a C)
    (-completedAdicKoszulOneSubShift T d r a D)
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    { left := reconstructionKoszulProductMap T d r a h
      right := reconstructionKoszulProductMap T d r a h
      w := reconstructionKoszulProductMap_comm T d r a h })⟦(-1 : ℤ)⟧'

private theorem reconstructionKoszulProductMap_id (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    reconstructionKoszulProductMap T d r a (𝟙 C) = 𝟙 _ := by
  apply Limits.Pi.hom_ext
  intro m
  simp only [reconstructionKoszulProductMap, Limits.Pi.map_π,
    HomologicalComplex.mapBifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, HomologicalComplex₂.total.map_id]
  exact Category.comp_id (Pi.π (completedAdicKoszulTensor T d r a C) m)

private theorem reconstructionKoszulProductMap_comp (r : ℕ) (a : Fin r → A)
    {C D E : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) (k : D ⟶ E) :
    reconstructionKoszulProductMap T d r a (h ≫ k) =
      reconstructionKoszulProductMap T d r a h ≫ reconstructionKoszulProductMap T d r a k := by
  apply Limits.Pi.hom_ext
  intro m
  simp [reconstructionKoszulProductMap, HomologicalComplex.mapBifunctorMap,
    Functor.map_comp, Category.assoc]

/-- The induced fibre map preserves identities. -/
theorem reconstructionKoszulFiberMap_id (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (CompletedAdicModules T d) ℤ) :
    reconstructionKoszulFiberMap T d r a (𝟙 C) = 𝟙 _ := by
  unfold reconstructionKoszulFiberMap
  simp only [reconstructionKoszulProductMap_id]
  change (shiftFunctor _ (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ (𝟙 _)) = _
  rw [HomologicalComplex.homotopyCofiber.mapArrowHom_id]
  exact (shiftFunctor _ (-1 : ℤ)).map_id _

/-- The induced fibre map preserves composition. -/
theorem reconstructionKoszulFiberMap_comp (r : ℕ) (a : Fin r → A)
    {C D E : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) (k : D ⟶ E) :
    reconstructionKoszulFiberMap T d r a (h ≫ k) =
      reconstructionKoszulFiberMap T d r a h ≫ reconstructionKoszulFiberMap T d r a k := by
  let α : Arrow.mk (-completedAdicKoszulOneSubShift T d r a C) ⟶
      Arrow.mk (-completedAdicKoszulOneSubShift T d r a D) :=
    { left := reconstructionKoszulProductMap T d r a h
      right := reconstructionKoszulProductMap T d r a h
      w := reconstructionKoszulProductMap_comm T d r a h }
  let β : Arrow.mk (-completedAdicKoszulOneSubShift T d r a D) ⟶
      Arrow.mk (-completedAdicKoszulOneSubShift T d r a E) :=
    { left := reconstructionKoszulProductMap T d r a k
      right := reconstructionKoszulProductMap T d r a k
      w := reconstructionKoszulProductMap_comm T d r a k }
  let γ : Arrow.mk (-completedAdicKoszulOneSubShift T d r a C) ⟶
      Arrow.mk (-completedAdicKoszulOneSubShift T d r a E) :=
    { left := reconstructionKoszulProductMap T d r a (h ≫ k)
      right := reconstructionKoszulProductMap T d r a (h ≫ k)
      w := reconstructionKoszulProductMap_comm T d r a (h ≫ k) }
  have hγ : γ = α ≫ β := by
    apply Arrow.hom_ext <;> exact reconstructionKoszulProductMap_comp T d r a h k
  change (shiftFunctor _ (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ γ) =
    (shiftFunctor _ (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ α) ≫
    (shiftFunctor _ (-1 : ℤ)).map
      (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ β)
  rw [hγ, HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
  exact (shiftFunctor _ (-1 : ℤ)).map_comp _ _

/-- Functoriality on complexes of the existing explicit Koszul fibre model. -/
def reconstructionKoszulFiberFunctor (r : ℕ) (a : Fin r → A) :
    CochainComplex (CompletedAdicModules T d) ℤ ⥤ CochainComplex (CompletedAdicModules T d) ℤ where
  obj := completedAdicKoszulFibre T d r a
  map := reconstructionKoszulFiberMap T d r a
  map_id := reconstructionKoszulFiberMap_id T d r a
  map_comp := reconstructionKoszulFiberMap_comp T d r a

section QuasiIsoHelpers

universe u v
variable {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory B]
  {X Y X' Y' : CochainComplex B ℤ} (f : X ⟶ Y) (g : X' ⟶ Y')
  (α : Arrow.mk f ⟶ Arrow.mk g)
set_option backward.isDefEq.respectTransparency false in
private theorem reconstructionConeMap_quasiIso [QuasiIso α.left] [QuasiIso α.right] :
    QuasiIso (CochainComplex.mappingCone.map f g α.left α.right α.w.symm) := by
  let t := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap f g α.left α.right α.w.symm)
  have ht : IsIso t.hom₃ := Pretriangulated.isIso₃_of_isIso₁₂ t
    (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (by change IsIso (DerivedCategory.Q.map α.left)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
    (by change IsIso (DerivedCategory.Q.map α.right)
        exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2 inferInstance)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso B _).1 ht

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory B] in
private theorem reconstructionConeArrowMap_eq : HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α =
      CochainComplex.mappingCone.map f g α.left α.right α.w.symm := by
  ext n : 1
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n + 1) n rfl
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inlX_desc_f,
      Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
      Pi.zero_apply, zero_add, add_zero,
      ]
    change _ = (CochainComplex.mappingCone.inl f).v (n + 1) n (by omega) ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.comp_v _ _ _ (n + 1) (n + 1) n (by omega) (by omega)]
    rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ (n + 1) n rfl]
    simp only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.mappingCone.inl, CochainComplex.HomComplex.Cochain.mk_v]
  · simp only [HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inrX_desc_f]
    change _ = (CochainComplex.mappingCone.inr f).f n ≫
      (CochainComplex.mappingCone.map f g α.left α.right α.w.symm).f n
    unfold CochainComplex.mappingCone.map
    rw [CochainComplex.mappingCone.inr_f_desc_f]
    rfl

variable {B : Type u} [Category.{v} B] [Abelian B]
  [HasCountableProducts B] [HasExactLimitsOfShape (Discrete ℕ) B]
private theorem reconstructionProduct_quasiIso (F G : ℕ → CochainComplex B ℤ) (f : ∀ n, F n ⟶ G n)
    [∀ n, QuasiIso (f n)] : QuasiIso (Limits.Pi.map f) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor B (.up ℤ) i
  have (n : ℕ) : IsIso (H.map (f n)) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f n) i).1 inferInstance
  have he : H.map (Limits.Pi.map f) ≫ piComparison H G =
      piComparison H F ≫ Limits.Pi.map (fun n ↦ H.map (f n)) := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, Limits.Pi.map_π,
      piComparison_comp_π_assoc, ← H.map_comp]
  have : IsIso (H.map (Limits.Pi.map f) ≫ piComparison H G) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (Limits.Pi.map f)) (piComparison H G)

end QuasiIsoHelpers

private theorem reconstructionCountableProducts_exact :
    HasExactLimitsOfShape (Discrete ℕ) (CompletedAdicModules T d) := by
  let B := CompletedAdicModules T d
  have hp (F G : ℕ → B) (f : ∀ n, F n ⟶ G n) (hf : ∀ n, Epi (f n)) :
      Epi (Limits.Pi.map f) :=
    (ProEt.countableProducts_exact.{t, 0, 0} T (completedAdicCommRing T d)).2.2 ℕ F G f hf
  have : (lim (J := Discrete ℕ) (C := B)).PreservesEpimorphisms := by
    constructor
    intro F G f hf
    have h : lim.map f = (Pi.isoLimit F).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit G).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp only [Category.assoc, Pi.isoLimit_hom_π, Limits.Pi.map_π,
        Pi.isoLimit_inv_π_assoc, ← limMap_eq, limMap_π]
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) :=
      hp (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩) (fun n ↦ f.app ⟨n⟩)
        (fun n ↦ inferInstance)
    rw [h]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi B (Discrete ℕ)

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The recorded Koszul model and its canonical maps descend through quasi-isomorphisms. -/
theorem reconstructionKoszulFiberFunctor_inverts (r : ℕ) (a : Fin r → A) :
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ)).IsInvertedBy
      (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q) := by
  let B := CompletedAdicModules T d
  let R := completedAdicCommRing T d
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI : MonoidalCategory B := SheafOfModules.monoidalCategory R
  letI : (curriedTensor B).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  letI : ∀ M : B, ((curriedTensor B).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R M
  have : HasExactLimitsOfShape (Discrete ℕ) B := reconstructionCountableProducts_exact T d
  intro C D h hh
  have : QuasiIso h := hh
  have hten (m : ℕ) : QuasiIso (HomologicalComplex.mapBifunctorMap h
      (𝟙 (completedAdicKoszul T d r a m)) (curriedTensor B) (.up ℤ)) := by
    have hk := CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R
      (completedAdicKoszul T d r a m) (completedAdicKoszul_isKFlat T d r a m) h hh
    dsimp only [CategoryTheory.koszulTensorFunctor, Functor.map₂CochainComplex,
      Functor.map₂HomologicalComplex, Functor.flip] at hk
    convert hk using 1 <;> rfl
  letI := hten
  have hp : QuasiIso (reconstructionKoszulProductMap T d r a h) := by
    dsimp only [reconstructionKoszulProductMap]
    exact reconstructionProduct_quasiIso _ _ _
  let α : Arrow.mk (-completedAdicKoszulOneSubShift T d r a C) ⟶
      Arrow.mk (-completedAdicKoszulOneSubShift T d r a D) :=
    { left := reconstructionKoszulProductMap T d r a h
      right := reconstructionKoszulProductMap T d r a h
      w := reconstructionKoszulProductMap_comm T d r a h }
  have hc : QuasiIso (HomologicalComplex.homotopyCofiber.mapArrowHom _ _
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α) := by
    rw [reconstructionConeArrowMap_eq]
    exact reconstructionConeMap_quasiIso _ _ α
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso B _).2
  change QuasiIso ((HomologicalComplex.homotopyCofiber.mapArrowHom _ _
    (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) α)⟦(-1 : ℤ)⟧')
  exact (CochainComplex.quasiIso_shift_iff _ _).2 hc

/-- The functor on the derived category induced by the existing Koszul fibre construction. -/
abbrev reconstructionKoszulDerivedFunctor (r : ℕ) (a : Fin r → A) :
    DerivedCategory (CompletedAdicModules T d) ⥤ DerivedCategory (CompletedAdicModules T d) :=
  Localization.lift (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (reconstructionKoszulFiberFunctor_inverts T d r a) DerivedCategory.Q

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The existing unit c to (u_C(c),0) is natural for the induced fibre maps. -/
theorem reconstructionKoszulUnit_naturality (r : ℕ) (a : Fin r → A)
    {C D : CochainComplex (CompletedAdicModules T d) ℤ} (h : C ⟶ D) :
    h ≫ completedAdicKoszulUnitComplex T d r a D =
      completedAdicKoszulUnitComplex T d r a C ≫ reconstructionKoszulFiberMap T d r a h := by
  letI : (curriedTensor (CompletedAdicModules T d)).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
      (completedAdicCommRing T d)
  letI : ∀ M : CompletedAdicModules T d,
      ((curriedTensor (CompletedAdicModules T d)).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
      (completedAdicCommRing T d) M
  have hu : h ≫ completedAdicKoszulProductUnit T d r a D =
      completedAdicKoszulProductUnit T d r a C ≫
        reconstructionKoszulProductMap T d r a h := by
    apply Limits.Pi.hom_ext
    intro m
    simp only [Category.assoc, completedAdicKoszulProductUnit,
      reconstructionKoszulProductMap, Limits.Pi.map_π, Limits.Pi.lift_comp_π,
      Limits.Pi.lift_comp_π_assoc]
    ext p : 1
    dsimp only [HomologicalComplex.comp_f, completedAdicKoszulTensorUnit]
    dsimp only [completedAdicKoszulTensorUnitF]
    rw [Category.assoc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f]
    change h.f p ≫ (ρ_ (D.X p)).inv ≫
        (D.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫ _ = _
    rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc]
    change (ρ_ (C.X p)).inv ≫
        (h.f p ▷ SheafOfModules.unit (completedAdicRing T d)) ≫
          (D.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫ _ =
      (ρ_ (C.X p)).inv ≫ (C.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫
        (h.f p ▷ (completedAdicKoszul T d r a m).X 0) ≫ _
    rw [← whisker_exchange_assoc]
    have hid := congrArg (fun z ↦ z ≫
      HomologicalComplex.ιMapBifunctor D (completedAdicKoszul T d r a m)
        (curriedTensor (CompletedAdicModules T d)) (ComplexShape.up ℤ) p 0 p (by simp))
      (((curriedTensor (CompletedAdicModules T d)).obj (D.X p)).map_id
        ((completedAdicKoszul T d r a m).X 0))
    exact congrArg (fun z ↦ (ρ_ (C.X p)).inv ≫
      (C.X p ◁ completedAdicKoszulUnitZero T d r a m) ≫
        (h.f p ▷ (completedAdicKoszul T d r a m).X 0) ≫ z)
      (hid.trans (Category.id_comp _)).symm
  ext p : 1
  dsimp only [HomologicalComplex.comp_f, completedAdicKoszulUnitComplex]
  rw [Category.assoc]
  dsimp only [reconstructionKoszulFiberMap]
  rw [CochainComplex.shiftFunctor_map_f']
  rw [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  dsimp only [Arrow.Hom.left]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    congrArg (fun f ↦ f.f p ≫
      HomologicalComplex.homotopyCofiber.inlX
        (-completedAdicKoszulOneSubShift T d r a D) p (p + (-1)) (by
          change p + (-1) + 1 = p
          omega)) hu

/-- The recorded degree-zero unit, assembled as a natural transformation of complexes. -/
def reconstructionKoszulComplexUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (CochainComplex (CompletedAdicModules T d) ℤ) ⟶
      reconstructionKoszulFiberFunctor T d r a where
  app := completedAdicKoszulUnitComplex T d r a
  naturality _ _ h := reconstructionKoszulUnit_naturality T d r a h

/-- Localization of the existing completion unit gives κ on the derived category. -/
def reconstructionKoszulDerivedUnit (r : ℕ) (a : Fin r → A) :
    𝟭 (DerivedCategory (CompletedAdicModules T d)) ⟶
      reconstructionKoszulDerivedFunctor T d r a :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      DerivedCategory.Q (𝟭 (DerivedCategory (CompletedAdicModules T d))) :=
    ⟨Functor.rightUnitor _⟩
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
      (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
      (reconstructionKoszulDerivedFunctor T d r a) :=
    Localization.liftingLift _ (reconstructionKoszulFiberFunctor_inverts T d r a) _
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (CompletedAdicModules T d) (ComplexShape.up ℤ))
    DerivedCategory.Q (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (𝟭 _) (reconstructionKoszulDerivedFunctor T d r a)
    (Functor.whiskerRight (reconstructionKoszulComplexUnit T d r a) DerivedCategory.Q)

/-- The functorial model uses the recorded intrinsic completion and its same unit. -/
theorem reconstructionKoszulIntrinsicComparison (r : ℕ) (a : Fin r → A)
    (K : DerivedCategory (CompletedAdicModules T d)) :
    ∃ j : (reconstructionKoszulDerivedFunctor T d r a).obj K ≅
        completedAdicIntrinsicCompletion T d r a K,
      (reconstructionKoszulDerivedUnit T d r a).app K ≫ j.hom =
        completedAdicIntrinsicUnit T d r a K := by
  let F := reconstructionKoszulDerivedFunctor T d r a
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let f := Localization.fac
    (reconstructionKoszulFiberFunctor T d r a ⋙ DerivedCategory.Q)
    (reconstructionKoszulFiberFunctor_inverts T d r a) DerivedCategory.Q
  refine ⟨F.mapIso e.symm ≪≫ f.app P, ?_⟩
  change (reconstructionKoszulDerivedUnit T d r a).app K ≫
    F.map e.inv ≫ f.hom.app P =
    e.inv ≫ DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a P)
  rw [← Category.assoc, ← (reconstructionKoszulDerivedUnit T d r a).naturality e.inv,
    Category.assoc]
  congr 1
  dsimp [reconstructionKoszulDerivedUnit]
  rw [Localization.liftNatTrans_app]
  change (𝟙 _ ≫ DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a P) ≫
    f.inv.app P) ≫ f.hom.app P = _
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id (DerivedCategory.Q.map (completedAdicKoszulUnitComplex T d r a P))

end AlgebraicGeometry.Scheme
