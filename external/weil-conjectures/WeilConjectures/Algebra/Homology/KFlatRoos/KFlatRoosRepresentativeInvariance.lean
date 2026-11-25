/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
/-!
# Invariance of augmented scalar-extension Roos complexes

Source: Stacks Project, Tags 06YS, 06YT, 06YY and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
The tower is indexed by n in N, corresponding to positive level n+1. Its algebra
structure is the natural transformation from the constant ring sheaf R. All tensor
objects use the recorded site tensor. The Roos complex has precisely the coordinates
V^i plus V^(i-1), differential (dx, (1-s)x-dy), and augmentation (p tensor 1, 0).
The helper existence statements uniquely determine maps on every section; no object
is selected from an unnormalized existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.KFlatRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  {R : Sheaf J CommRingCat.{r}}

/-- The existing module category of the underlying ring sheaf.
Source: Stacks Tag 03DA (blueprint: lem-pe-kflat-roos-representative-invariance). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- An R-algebra sheaf as an R-module, by the existing restriction of scalars.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModule {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) : Modules R :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map ι)).obj
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

-- Retain the existing instance binders in the public API.
set_option linter.unusedSectionVars false in
/-- The algebra map has a unique R-linear sheaf map with its original section values.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the equation on structure maps makes the sectionwise ring homomorphism
R-linear. Ring-map naturality makes these linear maps a sheaf morphism. Conversely,
the displayed value on every section determines every component, hence the map. -/
theorem algebraModuleMap_existsUnique {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :
    ∃! a : algebraModule ι ⟶ algebraModule ι',
      ∀ (U : Cᵒᵖ) (b : B.obj.obj U), a.val.app U b = f.hom.app U b := by
  let a : algebraModule ι ⟶ algebraModule ι' :=
    ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (algebraModule ι).val.obj U) (Y := (algebraModule ι').val.obj U)
        { toFun := f.hom.app U
          map_add' := map_add _
          map_smul' := by
            intro r b
            change B.obj.obj U at b
            change R.obj.obj U at r
            change f.hom.app U (ι.hom.app U r * b) =
              ι'.hom.app U r * f.hom.app U b
            rw [map_mul]
            have hh := congrArg (fun g : R ⟶ B' ↦ g.hom.app U r) h
            exact congrArg (fun z ↦ z * f.hom.app U b) hh }
       naturality := by
         intro U V g
         ext b
         exact ConcreteCategory.congr_hom (f.hom.naturality g) b }⟩
  refine ⟨a, fun _ _ ↦ rfl, ?_⟩
  intro a' ha'
  ext U b
  exact ha' U b

/-- The uniquely normalized map of underlying algebra modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def algebraModuleMap {B B' : Sheaf J CommRingCat.{r}}
    (ι : R ⟶ B) (ι' : R ⟶ B') (f : B ⟶ B') (h : ι ≫ f = ι') :=
  (algebraModuleMap_existsUnique ι ι' f h).exists.choose

set_option linter.unusedSectionVars false in
/-- The unit of scalar extension, uniquely specified on all local sections.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: p to p tensor 1 is additive, R-linear and commutes with restrictions;
compose with the module-sheafification unit. It is natural in the input module.
Every component is determined on every section, so this transformation is unique. -/
theorem tensorUnit_existsUnique {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :
    ∃! η : 𝟭 (Modules R) ⟶ siteSheafTensorRight (algebraModule ι),
      ∀ (M : Modules R) (U : Cᵒᵖ) (p : M.val.obj U),
        (η.app M).val.app U p = siteSheafTensorTmul M (algebraModule ι) U p (1 : B.obj.obj U) := by
  let q (M : Modules R) : M.val ⟶ siteTensorPresheaf M.val (algebraModule ι).val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := M.val.obj U)
        (Y := (siteTensorPresheaf M.val (algebraModule ι).val).obj U)
        ((TensorProduct.mk (R.obj.obj U) (M.val.obj U)
          ((algebraModule ι).val.obj U)).flip (1 : B.obj.obj U))
      naturality := by
        intro U V g
        ext p
        change (show M.val.obj V from M.val.map g p) ⊗ₜ[R.obj.obj V]
            (show (algebraModule ι).val.obj V from (1 : B.obj.obj V)) =
          (show M.val.obj V from M.val.map g p) ⊗ₜ[R.obj.obj V]
            (show (algebraModule ι).val.obj V from
              (algebraModule ι).val.map g
                (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)))
        have h_one : (algebraModule ι).val.map g
            (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)) =
              (show (algebraModule ι).val.obj V from (1 : B.obj.obj V)) :=
          map_one (B.obj.map g).hom
        rw [h_one] }
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let η : 𝟭 (Modules R) ⟶ siteSheafTensorRight (algebraModule ι) :=
    { app := fun M ↦ ⟨q M ≫ adj.unit.app _⟩
      naturality := by
        intro M N f
        apply SheafOfModules.hom_ext
        change f.val ≫ (q N ≫ adj.unit.app _) =
          (q M ≫ adj.unit.app _) ≫
            ((PresheafOfModules.sheafification
              (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
              (𝟙 _)).map (siteTensorHom f.val (algebraModule ι).val)).val
        ext U p
        have hf := adj.unit.naturality (siteTensorHom f.val (algebraModule ι).val)
        have hf' := congrArg (fun g ↦ (g.app U) (p ⊗ₜ[R.obj.obj U]
          (show (algebraModule ι).val.obj U from (1 : B.obj.obj U)))) hf
        exact hf' }
  refine ⟨η, fun _ _ _ ↦ rfl, ?_⟩
  intro η' hη'
  ext M U p
  exact hη' M U p

/-- The actual scalar-extension unit, with the prescribed pure-tensor formula.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def tensorUnit {B : Sheaf J CommRingCat.{r}} (ι : R ⟶ B) :=
  (tensorUnit_existsUnique ι).exists.choose

set_option linter.unusedSectionVars false in
private theorem tensorSecondMap_tmul
    (M N N' : Modules R) (g : N ⟶ N') (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (siteSheafTensorSecondMap M g).val.app U (siteSheafTensorTmul M N U x y) =
      siteSheafTensorTmul M N' U x (g.val.app U y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  have h := adj.unit.naturality (siteTensorSecondMap M.val g.val)
  exact (congrArg (fun f ↦ f.app U (x ⊗ₜ[R.obj.obj U] y)) h).symm

variable (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r})
  (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B)

/-- The module sheaf B_n with its given R-action.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelModule (n : ℕ) : Modules R := algebraModule (ι.app (op n))

set_option linter.unusedSectionVars false in
/-- Compatibility of the algebra structure with the consecutive transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: naturality of ι at n+1 to n, followed by the identity law for the constant functor. -/
theorem structure_compatible (n : ℕ) :
    ι.app (op (n + 1)) ≫ B.map (homOfLE (Nat.le_succ n)).op = ι.app (op n) := by
  simpa using (ι.naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The given transition, regarded as an R-module sheaf map.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def levelMap (n : ℕ) : levelModule B ι (n + 1) ⟶ levelModule B ι n :=
  algebraModuleMap (ι.app (op (n + 1))) (ι.app (op n))
    (B.map (homOfLE (Nat.le_succ n)).op) (structure_compatible B ι n)

/-- Termwise scalar extension, restricted back to R-modules.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def level (n : ℕ) : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (siteSheafTensorRight (levelModule B ι n)).mapHomologicalComplex (.up ℤ)

/-- Strict tensor transition induced by the algebra transition.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def transition (P : CochainComplex (Modules R) ℤ) (n : ℕ) :
    (level B ι (n + 1)).obj P ⟶ (level B ι n).obj P :=
  (NatTrans.mapHomologicalComplex (siteSheafTensorRightMap (levelMap B ι n)) (.up ℤ)).app P

private theorem tensorUnit_levelMap (n : ℕ) :
    tensorUnit (ι.app (op (n + 1))) ≫ siteSheafTensorRightMap (levelMap B ι n) =
      tensorUnit (ι.app (op n)) := by
  ext M U p
  change (siteSheafTensorSecondMap M (levelMap B ι n)).val.app U
      ((tensorUnit (ι.app (op (n + 1)))).app M |>.val.app U p) =
    ((tensorUnit (ι.app (op n))).app M).val.app U p
  dsimp only [tensorUnit, levelModule]
  rw [(tensorUnit_existsUnique (ι.app (op (n + 1)))).exists.choose_spec,
    (tensorUnit_existsUnique (ι.app (op n))).exists.choose_spec,
    tensorSecondMap_tmul]
  have hm := (algebraModuleMap_existsUnique
    (ι.app (op (n + 1))) (ι.app (op n))
    (B.map (homOfLE (Nat.le_succ n)).op) (structure_compatible B ι n)).exists.choose_spec
  change siteSheafTensorTmul M (levelModule B ι n) U p
      ((levelMap B ι n).val.app U (1 : (B.obj (op (n + 1))).obj.obj U)) = _
  congr 1
  exact (hm U (1 : (B.obj (op (n + 1))).obj.obj U)).trans
    (map_one ((B.map (homOfLE (Nat.le_succ n)).op).hom.app U).hom)

variable [HasCountableProducts (Modules R)]

/-- The termwise product V(P) of the scalar-extension tower.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def product (P : CochainComplex (Modules R) ℤ) :=
  ∏ᶜ fun n : ℕ => (level B ι n).obj P

/-- The endomorphism 1-s, whose nth coordinate is pr_n minus t_n pr_(n+1).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def oneSubShift (P : CochainComplex (Modules R) ℤ) : product B ι P ⟶ product B ι P :=
  Pi.lift (fun n => Pi.π (fun k : ℕ => (level B ι k).obj P) n -
    Pi.π (fun k : ℕ => (level B ι k).obj P) (n + 1) ≫ transition B ι P n)

/-- The two coordinates of L(P) in degree i, in the order used in the node.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosX (P : CochainComplex (Modules R) ℤ) (i : ℤ) :=
  (product B ι P).X i ⊞ (product B ι P).X (i - 1)

/-- The differential (x,y) to (dx,(1-s)x-dy).
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosD (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosX B ι P i ⟶ roosX B ι P (i + 1) :=
  biprod.lift (biprod.fst ≫ (product B ι P).d i (i + 1))
    (biprod.fst ≫ (oneSubShift B ι P).f i ≫
      eqToHom (congrArg (product B ι P).X (Int.add_sub_cancel i 1).symm) -
      biprod.snd ≫ (product B ι P).d (i - 1) ((i + 1) - 1))

set_option linter.unusedSectionVars false in
/-- The displayed Roos differential squares to zero.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: the first coordinate is d squared, hence zero. The second is
(1-s)dx-d(1-s)x+d squared y; 1-s is a chain map, so these terms cancel. -/
theorem roosD_sq (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    roosD B ι P i ≫ roosD B ι P (i + 1) = 0 := by
  apply biprod.hom_ext
  · simp [roosD, Category.assoc]
  · simp +instances only [roosX, roosD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.lift_fst_assoc,
      eqToHom_naturality_assoc, eqToHom_refl, Category.id_comp, biprod.lift_snd_assoc,
      Preadditive.sub_comp, HomologicalComplex.Hom.comm, HomologicalComplex.d_comp_d,
      comp_zero, sub_zero, zero_comp]
    apply sub_eq_zero.mpr
    have hd := eqToHom_naturality
      (fun j : ℤ ↦ (product B ι P).d j (i + 1 + 1 - 1))
      (Int.add_sub_cancel i 1).symm
    simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using
      congrArg (fun f ↦ biprod.fst ≫ f ≫
        (oneSubShift B ι P).f (i + 1 + 1 - 1)) hd

/-- The specified Roos complex, with real objects and differential.
Source: Stacks Tag 08TC (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roos (P : CochainComplex (Modules R) ℤ) : CochainComplex (Modules R) ℤ :=
  CochainComplex.of (roosX B ι P) (roosD B ι P) (roosD_sq B ι P)

/-- The product of the tensor units in degree i.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def unitProduct (P : CochainComplex (Modules R) ℤ) : P ⟶ product B ι P :=
  Pi.lift (fun n =>
    (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op n))) (.up ℤ)).app P)

set_option linter.unusedSectionVars false in
private theorem unitProduct_oneSubShift (P : CochainComplex (Modules R) ℤ) :
    unitProduct B ι P ≫ oneSubShift B ι P = 0 := by
  apply Pi.hom_ext
  intro n
  have hunit :
      (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op (n + 1)))) (.up ℤ)).app P ≫
          transition B ι P n =
        (NatTrans.mapHomologicalComplex (tensorUnit (ι.app (op n))) (.up ℤ)).app P := by
    ext j : 1
    exact congrArg (fun η ↦ η.app (P.X j)) (tensorUnit_levelMap B ι n)
  simp [unitProduct, oneSubShift, Category.assoc, Preadditive.comp_sub, hunit]

/-- The augmentation (unit,0) commutes with differentials.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor units commute with d. The algebra transitions preserve 1, so
(1-s) composed with the product unit is zero, giving the second coordinate. -/
theorem augmentation_comm (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    biprod.lift ((unitProduct B ι P).f i) 0 ≫ (roos B ι P).d i (i + 1) =
      P.d i (i + 1) ≫ biprod.lift ((unitProduct B ι P).f (i + 1)) 0 := by
  have hunit (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j)
    (unitProduct_oneSubShift B ι P)
  dsimp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hunit
  simp only [roos, CochainComplex.of_d]
  apply biprod.hom_ext
  · simp [roosD, Category.assoc]
  · simp [roosD, Category.assoc, hunit]

/-- The actual augmentation p to ((p tensor 1)_n,0).
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def augmentation (P : CochainComplex (Modules R) ℤ) : P ⟶ roos B ι P :=
  CochainComplex.ofHom (fun i => biprod.lift ((unitProduct B ι P).f i) 0)
    (augmentation_comm B ι P)

/-- The product of a tensor B_n over all levels.
Source: Stacks Tag 03EK (blueprint: lem-pe-kflat-roos-representative-invariance). -/
def productMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    product B ι P ⟶ product B ι P' :=
  Limits.Pi.map (fun n => (level B ι n).map a)

set_option linter.unusedSectionVars false in
private theorem productMap_oneSubShift {P P' : CochainComplex (Modules R) ℤ}
    (a : P ⟶ P') :
    productMap B ι a ≫ oneSubShift B ι P' =
      oneSubShift B ι P ≫ productMap B ι a := by
  apply Pi.hom_ext
  intro n
  have ht := (NatTrans.mapHomologicalComplex
    (siteSheafTensorRightMap (levelMap B ι n)) (.up ℤ)).naturality a
  change (level B ι (n + 1)).map a ≫ transition B ι P' n =
    transition B ι P n ≫ (level B ι n).map a at ht
  simp [productMap, oneSubShift, Category.assoc, Preadditive.comp_sub,
    Preadditive.sub_comp, ht]

/-- The diagonal product map commutes with the specified differential.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance).
Proof: tensor naturality makes a tensor B_n commute with transition maps. Thus
its product commutes with 1-s as well as d; multiply the two-by-two matrices. -/
theorem roosMap_comm {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') (i : ℤ) :
    biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)) ≫
        (roos B ι P').d i (i + 1) =
      (roos B ι P).d i (i + 1) ≫
        biprod.map ((productMap B ι a).f (i + 1)) ((productMap B ι a).f ((i + 1) - 1)) := by
  have hs (j : ℤ) := congrArg (fun f ↦ HomologicalComplex.Hom.f f j)
    (productMap_oneSubShift B ι a)
  dsimp only [HomologicalComplex.comp_f] at hs
  simp only [roos, CochainComplex.of_d]
  apply biprod.hom_ext
  · simp +instances [roosD, roosX, Category.assoc]
  · simp +instances only [roosX, roosD, add_sub_cancel_right, eqToHom_naturality,
      Category.assoc, biprod.lift_snd, Preadditive.comp_sub, biprod.map_fst_assoc,
      eqToHom_naturality_assoc, biprod.map_snd_assoc, HomologicalComplex.Hom.comm,
      biprod.map_snd, biprod.lift_snd_assoc, Preadditive.sub_comp, sub_left_inj]
    rw [hs (i + 1 - 1)]

/-- L(a) applies the product of a tensor B_n to both coordinates.
Source: Stacks Tags 03EK and 08TC
(blueprint: lem-pe-kflat-roos-representative-invariance). -/
def roosMap {P P' : CochainComplex (Modules R) ℤ} (a : P ⟶ P') :
    roos B ι P ⟶ roos B ι P' :=
  CochainComplex.ofHom
    (fun i => biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)))
    (roosMap_comm B ι a)

private theorem augmentation_naturality {P P' : CochainComplex (Modules R) ℤ}
    (a : P ⟶ P') :
    augmentation B ι P ≫ roosMap B ι a = a ≫ augmentation B ι P' := by
  ext i : 1
  change biprod.lift ((unitProduct B ι P).f i) 0 ≫
    biprod.map ((productMap B ι a).f i) ((productMap B ι a).f (i - 1)) =
      a.f i ≫ biprod.lift ((unitProduct B ι P').f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    have h : unitProduct B ι P ≫ productMap B ι a = a ≫ unitProduct B ι P' := by
      apply Pi.hom_ext
      intro n
      simp only [unitProduct, productMap, Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc,
        Pi.lift_comp_π]
      exact ((NatTrans.mapHomologicalComplex
        (tensorUnit (ι.app (op n))) (.up ℤ)).naturality a).symm
    exact congrArg (fun f ↦ f.f i) h
  · simp

-- Elaborating the tensor square and single-complex comparison needs extra heartbeats.
end SheafOfModules.KFlatRoos
