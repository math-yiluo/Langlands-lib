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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-! # The unbounded scalar model of an ind-finite-free algebra sheaf

Source: Stacks Project, sites-modules.tex, Tags 03EU (2), 03EP (2), and Section 03EK;
sites-cohomology.tex, Tags 06YT and 06YY; derived.tex, Tag 015F.
(blueprint: lem-sfb-ind-finite-free-scalar-model).
The auxiliary functors spell out the coefficient diagram and its termwise tensor colimit.
All derived scalar extensions are the existing universal cochain models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wT
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules.IndFiniteFree

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]

/-- The existing module category at the coefficient universe.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev Modules (R : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J R)

/-- Ordinary scalar restriction, with the same sections and restricted action.
Source: Stacks 03D2 (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
abbrev restriction {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S) :
    Modules S ⥤ Modules R :=
  restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)

/-- Forget the algebra structure of an algebra sheaf, retaining its R-module structure.
On morphisms this is the original section map, linear by the triangle over R.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def algebraModules (R : Sheaf J CommRingCat.{r}) : Under R ⥤ Modules R where
  obj A := (restriction A.hom).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A.right))
  map {A B} f :=
    { val := PresheafOfModules.homMk
        (Functor.whiskerRight f.right.hom
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) (by
          intro V x a
          change A.right.obj.obj V at a
          change R.obj.obj V at x
          change (f.right.hom.app V).hom ((A.hom.hom.app V).hom x * a) =
            (B.hom.hom.app V).hom x * (f.right.hom.app V).hom a
          rw [map_mul]
          congr 1
          exact congrArg (fun t ↦ t.hom.app V x) (Under.w f)) }

/-- Tensor a complex termwise with a coefficient module; coefficient maps act by tensor.
Source: Stacks 03EK (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorComplex (R : Sheaf J CommRingCat.{r}) :
    Modules R ⥤ (CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ) where
  obj M := (tensorLeft M).mapHomologicalComplex (.up ℤ)
  map f := ((curriedTensor (Modules R)).map f).mapHomologicalComplex (.up ℤ)
  map_id M := by simp
  map_comp f g := by simp

/-- The diagram i ↦ S_i tensor A, with all differentials and transitions termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorDiagram {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) (A : CochainComplex (Modules R) ℤ) :
    I ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip.obj A

/-- The actual colimit functor on these complexes. Colimits of complexes are termwise.
Source: Stacks 03EP (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def tensorColimit {R : Sheaf J CommRingCat.{r}} {I : Type r} [SmallCategory I]
    (D : I ⥤ Under R) :
    CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ :=
  (D ⋙ algebraModules R ⋙ tensorComplex R).flip ⋙ colim

/-- A pure tensor in the sheaf tensor, using its presheaf-to-sheaf unit.
The supplied factor is the actual underlying module, not a choice of basis.
Source: Stacks 03EK, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def pureTensor {R : Sheaf J CommRingCat.{r}} (M N : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) : (M ⊗ N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).unit.app
      (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y) |>
    (tensorObjIsoSheafification M N).inv.val.app V

private theorem pureTensor_ext {R : Sheaf J CommRingCat.{r}}
    {M N P : Modules R} (f g : M ⊗ N ⟶ P)
    (h : ∀ (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V),
      f.val.app V (pureTensor M N V x y) = g.val.app V (pureTensor M N V x y)) :
    f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) P).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  ext t
  change f.val.app V ((tensorObjIsoSheafification M N).inv.val.app V
      ((adj.unit.app (M.val ⊗ N.val)).app V t)) =
    g.val.app V ((tensorObjIsoSheafification M N).inv.val.app V
      ((adj.unit.app (M.val ⊗ N.val)).app V t))
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h V x y
  | add t t' ht ht' => simp only [map_add, ht, ht']

variable {R : Sheaf J CommRingCat.{r}} in
/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : Modules R)
    {T T' : Modules R} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

variable {R : Sheaf J CommRingCat.{r}} in
/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : Modules R}
    (f : A' ⟶ A) (T : Modules R) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private theorem pureTensor_whiskerRight {R : Sheaf J CommRingCat.{r}}
    {M M' : Modules R} (f : M ⟶ M') (N : Modules R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (f ▷ N).val.app V (pureTensor M N V x y) =
      pureTensor M' N V (f.val.app V x) y := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  have h : (tensorObjIsoSheafification M N).inv ≫ f ▷ N =
      (PresheafOfModules.sheafification (𝟙
        (derivedChangeRingIndependentCoefficients J R).obj)).map (f.val ▷ N.val) ≫
          (tensorObjIsoSheafification M' N).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerRight_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] y))
    (adj.unit.naturality (f.val ▷ N.val))
  have he := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))) h
  exact he.trans (congrArg ((tensorObjIsoSheafification M' N).inv.val.app V) hh.symm)

private theorem pureTensor_whiskerLeft {R : Sheaf J CommRingCat.{r}}
    (M : Modules R) {N N' : Modules R} (f : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (M ◁ f).val.app V (pureTensor M N V x y) =
      pureTensor M N' V x (f.val.app V y) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J R).obj)
  have h : (tensorObjIsoSheafification M N).inv ≫ M ◁ f =
      (PresheafOfModules.sheafification (𝟙
        (derivedChangeRingIndependentCoefficients J R).obj)).map (M.val ◁ f.val) ≫
          (tensorObjIsoSheafification M N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerLeft_tensorObjIsoSheafification_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] y))
    (adj.unit.naturality (M.val ◁ f.val))
  have he := congrArg (fun k ↦ k.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[R.obj.obj V] y))) h
  exact he.trans (congrArg ((tensorObjIsoSheafification M N').inv.val.app V) hh.symm)

private theorem tensorLeft_colimit_finiteLimits {R : Sheaf J CommRingCat.{r}}
    {K : Type r} [SmallCategory K] [HasExactColimitsOfShape K (Modules R)]
    (F : K ⥤ Modules R) (c : Cocone F) (hc : IsColimit c)
    (h : ∀ k, PreservesFiniteLimits (tensorLeft (F.obj k))) :
    PreservesFiniteLimits (tensorLeft c.pt) := by
  have hcol (M : Modules R) : PreservesColimitsOfSize.{r, r} (tensorRight M) := by
    have := tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have : PreservesColimit F (curriedTensor (Modules R)) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor F
  let e : tensorLeft c.pt ≅ (F ⋙ curriedTensor (Modules R)).flip ⋙ colim :=
    (curriedTensor (Modules R)).mapIso (hc.coconePointUniqueUpToIso (colimit.isColimit F)) ≪≫
      preservesColimitIso (curriedTensor (Modules R)) F ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((F ⋙ curriedTensor (Modules R)).flip) :=
    preservesFiniteLimits_of_evaluation _ h
  have : PreservesFiniteLimits ((F ⋙ curriedTensor (Modules R)).flip ⋙ colim) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso e.symm

private theorem tensorLeft_finiteFree_finiteLimits {R : Sheaf J CommRingCat.{r}}
    (M : Modules R) (d : ℕ)
    (e : M ≅ ∏ᶜ fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)) :
    PreservesFiniteLimits (tensorLeft M) := by
  have : HasFiniteBiproducts (Modules R) := Abelian.hasFiniteBiproducts
  let U : Modules R := unit (derivedChangeRingIndependentCoefficients J R)
  let F : Discrete (ULift.{r} (Fin d)) ⥤ Modules R :=
    Discrete.functor (fun _ ↦ U)
  have : PreservesFiniteLimits (tensorLeft U) :=
    preservesFiniteLimits_of_natIso (leftUnitorNatIso (Modules R)).symm
  have : PreservesFiniteLimits (tensorLeft (colimit F)) :=
    tensorLeft_colimit_finiteLimits F (colimit.cocone F) (colimit.isColimit F)
      (fun _ ↦ inferInstanceAs (PreservesFiniteLimits (tensorLeft U)))
  let e' : M ≅ colimit F := e ≪≫
    (Pi.whiskerEquiv (Equiv.ulift : ULift.{r} (Fin d) ≃ Fin d) (fun _ ↦ Iso.refl U)).symm ≪≫
      (HasBiproductsOfShape.colimIsoLim.app F).symm
  exact preservesFiniteLimits_of_natIso ((curriedTensor (Modules R)).mapIso e').symm

section OrdinaryComparison

variable {R S : Sheaf J CommRingCat.{r}}

private def restrictedTensorPresheafIso (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheaf.{v, u, r} φ M) := by
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let ρ := (φ.hom.app V).hom
    let T := TensorProduct (R.obj.obj V)
      ((ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
      (M.val.obj V)
    change ModuleCat.of (R.obj.obj V) T ≅
      (ModuleCat.restrictScalars ρ).obj (ModuleCat.of (S.obj.obj V) T)
    exact (LinearEquiv.refl (R.obj.obj V) T).toModuleIso
  · intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul s m =>
      let : Module (R.obj.obj W)
          ((ModuleCat.restrictScalars
            (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj.map f).hom).obj
              (M.val.obj W)) := inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMap φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M f) s m).symm

section
variable {R₀ B₀ : Sheaf J RingCat.{r}}

private noncomputable def restrictionSheafificationComparison
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_isIso
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj) :
    IsIso (restrictionSheafificationComparison α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparison α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparison
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{r}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem restrictionSheafificationComparison_unit
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{r} B₀.obj)
    (W : Cᵒᵖ) (x : P.obj W) :
    (restrictionSheafificationComparison α P).val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 R₀.obj)).unit.app
          ((PresheafOfModules.restrictScalars α.hom).obj P)).app W x) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P).app W x := by
  have h := (PresheafOfModules.sheafificationHomEquiv
    (P := (PresheafOfModules.restrictScalars α.hom).obj P)
    (F := (restrictScalars α).obj
      ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P))
    (𝟙 R₀.obj)).apply_symm_apply
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))
  exact congrArg (fun k ↦ (k.app W) x) h

end

/-- The canonical map from the presheaf tensor to the underlying sheaf tensor.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison). -/
private def tensorPresheafUnit
    (M N : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
      (tensorObjIsoSheafification M N).inv.val

set_option maxHeartbeats 50000 in
-- Mixed tensor coefficient structures require additional elaboration.
/-- Restricted extension of scalars is tensoring with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-extension-tensor-comparison).

Proof: the presheaf tensor of the restricted target ring with M has exactly the
same section modules as restricted sectionwise scalar extension. Both restriction
maps send s tensor m to the tensor of the two restrictions, so the identity maps
form an isomorphism. Sheafify it over R. Restriction commutes with sheafification:
after forgetting to abelian sheaves the comparison is the identity of the same
sheafification, and forgetting reflects isomorphisms. Compose with the canonical
tensor-sheafification comparison. Naturality of the sheafification unit gives the
pure-tensor formula. No flatness or localization assumption is used. -/
private theorem exists_extensionTensorComparison (φ : R ⟶ S)
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (monoidalCategory R).tensorObj
        ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M ≅
        (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (changeOfRings.{v, u, r} φ M),
      ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
        e.hom.val.app V
          ((tensorPresheafUnit
            ((restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
              (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M).app V
            ((show ((restrictScalars.{r}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
                  (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val.obj V
              from s) ⊗ₜ[R.obj.obj V] m)) =
        (toSheafify J (changeOfRingsPresheaf.{v, u, r} φ M).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) := by
  let N := (restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let P := changeOfRingsPresheaf.{v, u, r} φ M
  let SR := PresheafOfModules.sheafification.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{r}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := restrictedTensorPresheafIso φ M
  have := restrictionSheafificationComparison_isIso
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P
  let e := tensorObjIsoSheafification N M ≪≫ SR.mapIso eP ≪≫
    asIso (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P)
  have he : (tensorObjIsoSheafification N M).inv ≫ e.hom =
      SR.map eP.hom ≫ restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Iso.inv_hom_id_assoc]
  clear_value e
  refine ⟨e, ?_⟩
  intro V s m
  have hn := adj.unit.naturality eP.hom
  have hn' := congrArg (fun k ↦ (k.app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) hn
  have hr' := restrictionSheafificationComparison_unit
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
  change ((tensorPresheafUnit N M ≫ e.hom.val).app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m) = _
  unfold tensorPresheafUnit
  rw [Category.assoc]
  change ((adj.unit.app (N.val ⊗ M.val) ≫
    ((tensorObjIsoSheafification N M).inv ≫ e.hom).val).app V) _ = _
  rw [he]
  change (restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V
    ((SR.map eP.hom).val.app V
      ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P)).app V
        (eP.hom.app V ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) =
      (SR.map eP.hom).val.app V ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) at hn'
  exact (congrArg ((restrictionSheafificationComparison
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V) hn'.symm).trans hr'

end OrdinaryComparison

variable {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]

/-- The pure tensor in the ordinary functor of the existing derived scalar model.
Source: Stacks 03EK, 06YY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def extensionPure (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (M : Modules R) (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (m.E.obj M).val.obj V :=
  (eqToHom (m.obj_eq M).symm).val.app V
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))

private theorem extensionPure_naturality
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    {M N : Modules R} (f : M ⟶ N) (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (m.E.map f).val.app V (extensionPure m M V s a) =
      extensionPure m N V s (f.val.app V a) := by
  let g : changeOfRingsPresheaf φ M ⟶ changeOfRingsPresheaf φ N :=
    { app := fun W ↦ (ModuleCat.extendScalars (φ.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality φ M f }
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
  have hn := congrArg (fun k ↦ k.app V (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))
    (adj.unit.naturality g)
  have hh : eqToHom (m.obj_eq M).symm ≫ m.E.map f =
      changeOfRingsHom φ M f ≫ eqToHom (m.obj_eq N).symm := by
    rw [m.map_eq]
    simp
  have he := congrArg (fun k ↦ k.val.app V
    ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
      (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] a))) hh
  exact he.trans (congrArg ((eqToHom (m.obj_eq N).symm).val.app V) hn.symm)

private noncomputable def restrictionComposition
    {T : Sheaf J CommRingCat.{r}} (ψ : S ⟶ T) (γ : R ⟶ T) (hγ : γ = φ ≫ ψ) :
    restriction ψ ⋙ restriction φ ≅ restriction γ :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦
      (ModuleCat.restrictScalarsComp'App (φ.hom.app V).hom (ψ.hom.app V).hom
        (γ.hom.app V).hom (congrArg (fun f ↦ (f.hom.app V).hom) hγ)
        (M.val.obj V)).symm) (by intros; ext x; rfl)))
    (by intros; ext V x; rfl)

private noncomputable def ordinaryIso
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) (M : Modules R) :
    (algebraModules R).obj (Under.mk φ) ⊗ M ≅ (restriction φ).obj (m.E.obj M) :=
  (exists_extensionTensorComparison φ M).choose ≪≫
    (restriction φ).mapIso (eqToIso (m.obj_eq M).symm)

private theorem ordinaryIso_pure
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) (M : Modules R)
    (V : Cᵒᵖ) (s : S.obj.obj V) (a : M.val.obj V) :
    (ordinaryIso m M).hom.val.app V
        (pureTensor ((algebraModules R).obj (Under.mk φ)) M V s a) =
      extensionPure m M V s a := by
  exact congrArg ((eqToHom (m.obj_eq M).symm).val.app V)
    ((exists_extensionTensorComparison φ M).choose_spec V s a)

private noncomputable def ordinaryComparison
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    tensorLeft ((algebraModules R).obj (Under.mk φ)) ≅ m.E ⋙ restriction φ :=
  NatIso.ofComponents (ordinaryIso m) (by
    intro M N f
    apply pureTensor_ext
    intro V s a
    change (ordinaryIso m N).hom.val.app V
        ((((algebraModules R).obj (Under.mk φ)) ◁ f).val.app V
          (pureTensor _ M V s a)) =
      (m.E.map f).val.app V
        ((ordinaryIso m M).hom.val.app V (pureTensor _ M V s a))
    rw [pureTensor_whiskerLeft, ordinaryIso_pure, ordinaryIso_pure,
      extensionPure_naturality])

/-- Normalization of the chain comparison on the sheafification-unit images of local
pure tensors. The coprojections are those of the supplied algebra colimit.
Source: Stacks 03EP, 03CY (blueprint: lem-sfb-ind-finite-free-scalar-model). -/
def Normalized {I : Type r} [SmallCategory I] (D : I ⥤ Under R) (c : Cocone D)
    [HasDerivedCategory.{wS} (Modules c.pt.right)]
    (m : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} c.pt.hom)
    (κ : tensorColimit D ≅ m.E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction c.pt.hom).mapHomologicalComplex (.up ℤ)) : Prop :=
  ∀ (A : CochainComplex (Modules R) ℤ) (i : I) (n : ℤ) (V : Cᵒᵖ)
    (s : (D.obj i).right.obj.obj V) (a : (A.X n).val.obj V),
    (((colimit.ι (tensorDiagram D A) i) ≫ κ.hom.app A).f n).val.app V
        (pureTensor ((algebraModules R).obj (D.obj i)) (A.X n) V s a) =
      extensionPure m (A.X n) V ((c.ι.app i).right.hom.app V s) a

end SheafOfModules.IndFiniteFree
