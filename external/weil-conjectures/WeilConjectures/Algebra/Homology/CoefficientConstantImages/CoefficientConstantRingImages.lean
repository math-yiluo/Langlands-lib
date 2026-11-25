/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import all WeilConjectures.CategoryTheory.GeometricRingInverseImage
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.LeftExact
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all WeilConjectures.CategoryTheory.InverseImageRingFunctor
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantComparison
import all Mathlib.CategoryTheory.Sites.Adjunction
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantRingOperations
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantSetComparison
import all Mathlib.CategoryTheory.Sites.GlobalSections
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.RouteInverseImageConstantRingAssembly
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Constant ring inverse images in an independent coefficient universe

Source: Stacks Project, Tags 00YV and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules.CoefficientConstantImages

private noncomputable abbrev typeLimits
    {T : Type uC} [Category.{vC} T] [EssentiallySmall.{w} T] :
    HasLimitsOfShape Tᵒᵖ (Type w) :=
  hasLimitsOfShape_of_essentiallySmall Tᵒᵖ (Type w)

private noncomputable abbrev typeSheafify
    {T : Type uC} [Category.{vC} T] [EssentiallySmall.{w} T]
    (J : GrothendieckTopology T) : HasSheafify J (Type w) :=
  hasSheafifyEssentiallySmallSite J (Type w)

attribute [local instance] typeLimits typeSheafify

private noncomputable abbrev ringSmallArrowLimits
    {T : Type uC} [Category.{vC} T] [EssentiallySmall.{w} T] (U : Tᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} T).inverse.op)
      CommRingCat.{w} :=
  HasLimitsOfShape.of_small.{w, w} CommRingCat.{w} _

private noncomputable abbrev typeSmallArrowLimits
    {T : Type uC} [Category.{vC} T] [EssentiallySmall.{w} T] (U : Tᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (equivSmallModel.{w} T).inverse.op) (Type w) :=
  HasLimitsOfShape.of_small.{w, w} (Type w) _

attribute [local instance] ringSmallArrowLimits typeSmallArrowLimits

private noncomputable abbrev ringForgetSheafification
    {T : Type uC} [Category.{vC} T] [EssentiallySmall.{w} T]
    (J : GrothendieckTopology T) :
    J.PreservesSheafification (CategoryTheory.forget CommRingCat.{w}) :=
  GrothendieckTopology.PreservesSheafification.transport (A := CommRingCat.{w}) J
    ((equivSmallModel.{w} T).inverse.inducedTopology J)
    (equivSmallModel.{w} T).inverse (Type w) (CategoryTheory.forget CommRingCat.{w})

attribute [local instance] ringForgetSheafification

private abbrev CoeffSet {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [HasWeakSheafify J CommRingCat.{w}] : Sheaf J (Type w) :=
  (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj
    ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ))

/-- Characterization of the addition map of the constant ring sheaf by its values
on sections. Source: Stacks, ring paragraph of the proof of 00YV
(blueprint: lem-pur-coefficient-constant-ring-images). -/
private def IsRingAdd {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [HasWeakSheafify J CommRingCat.{w}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) +
      @id (((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

/-- Characterization of the multiplication map of the constant ring sheaf by its
values on sections, in the given order (no commutativity). Source: Stacks, ring
paragraph of the proof of 00YV (blueprint: lem-pur-coefficient-constant-ring-images). -/
private def IsRingMul {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [HasWeakSheafify J CommRingCat.{w}]
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) : Prop :=
  ∀ (T : Cᵒᵖ) (x : (CoeffSet J Λ ⨯ CoeffSet J Λ).obj.obj T),
    m.hom.app T x =
      @id (((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T)
        ((prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x) *
      @id (((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T)
        ((prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T x)

section CoefficientConstruction
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
variable (R : Sheaf K (Type w) ⥤ Sheaf J (Type w))
variable (adj : L ⊣ R) [PreservesFiniteLimits L]
private def pointTerminal : IsTerminal ((constantSheaf J (Type w)).obj PUnit.{w + 1}) := by
  exact (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type w)) _
private def pointComparison :
    L.obj ((constantSheaf J (Type w)).obj PUnit.{w + 1}) ≅
      (constantSheaf K (Type w)).obj PUnit.{w + 1} :=
  ((pointTerminal J).isTerminalObj L _).uniqueUpToIso (pointTerminal K)
private def globalComparison : R ⋙ Sheaf.Γ J (Type w) ≅ Sheaf.Γ K (Type w) := by
  let p := pointComparison J K L
  let E (F : Sheaf K (Type w)) :
      (Sheaf.Γ J (Type w)).obj (R.obj F) ≃ (Sheaf.Γ K (Type w)).obj F :=
    (Sheaf.ΓObjEquivHom J (R.obj F) PUnit.{w + 1}).trans
      ((adj.homEquiv _ F).symm.trans
        ((Iso.homCongr p (Iso.refl F)).trans
          (Sheaf.ΓObjEquivHom K F PUnit.{w + 1}).symm))
  refine NatIso.ofComponents (fun F ↦ (E F).toIso) ?_
  intro F G f
  ext x
  change E G ((Sheaf.Γ J (Type w)).map (R.map f) x) =
    (Sheaf.Γ K (Type w)).map f (E F x)
  apply (Sheaf.ΓObjEquivHom K G PUnit.{w + 1}).injective
  rw [Sheaf.ΓObjEquivHom_naturality]
  simp only [E, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [Sheaf.ΓObjEquivHom_naturality, adj.homEquiv_naturality_right_symm]
  simp only [Category.assoc]
private def constantComparison :
    constantSheaf J (Type w) ⋙ L ≅ constantSheaf K (Type w) :=
  (((constantSheafΓAdj J (Type w)).comp adj).ofNatIsoRight
    (globalComparison J K L R adj)).leftAdjointUniq (constantSheafΓAdj K (Type w))

@[reassoc] private theorem constantComparison_naturality (X Y : Type w) (f : X ⟶ Y) :
    L.map ((constantSheaf J (Type w)).map f) ≫
        (constantComparison J K L R adj).hom.app Y =
      (constantComparison J K L R adj).hom.app X ≫ (constantSheaf K (Type w)).map f :=
  (constantComparison J K L R adj).hom.naturality f

variable (Λ : Type w) [CommRing Λ] [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}]

private def normalizedRingComparison :
    L.obj ((constantSheaf J (Type w)).obj Λ) ≅
      CoeffSet K Λ :=
  (constantComparison J K L R adj).app Λ ≪≫
    ((constantCommuteCompose K (CategoryTheory.forget CommRingCat.{w})).app (CommRingCat.of Λ)).symm

private theorem coeff_unit (T : Cᵒᵖ) (r : Λ) :
    ((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r) =
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app T r) := by
  have h := sheafComposeIso_hom_fac J (CategoryTheory.forget CommRingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) (CategoryTheory.forget CommRingCat.{w})).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ (CommRingCat.of Λ)
      (CategoryTheory.forget CommRingCat.{w})).inv) ≫
    (sheafifyComposeIso J (CategoryTheory.forget CommRingCat.{w})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).hom).app T) r = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

omit [HasWeakSheafify J CommRingCat.{w}] [EssentiallySmall.{w} C] in
private theorem constantMap_unit (X Y : Type w) (f : X → Y) (T : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type w)).map (TypeCat.ofHom f)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app T x) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app T (f x) := by
  exact (congrArg (fun g ↦ g.app T x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

private theorem ringAddition_constants
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) (hm : IsRingAdd J Λ m) :
    prod.lift
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)) ≫ m =
      (constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 + p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ) := by
  let q : (constantSheaf J (Type w)).obj (Λ × Λ) ⟶
      CoeffSet J Λ ⨯ CoeffSet J Λ :=
    prod.lift
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
  change q ≫ m = _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (CoeffSet J Λ).property
  ext T r
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  change m.hom.app T _ = _
  rw [hm]
  have hfst : (prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.fst = _ from prod.lift_fst _ _)
  have hsnd : (prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.snd = _ from prod.lift_snd _ _)
  erw [hfst, hsnd]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, constantMap_unit, id_eq]
  change (show ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.1))) +
    (show ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.2))) =
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      (((constantSheaf J (Type w)).map
        (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 + p.2))).hom.app T
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)))
  rw [constantMap_unit, coeff_unit, coeff_unit, coeff_unit]
  exact (map_add
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app T).hom) r.1 r.2).symm

private theorem ringMultiplication_constants
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ) (hm : IsRingMul J Λ m) :
    prod.lift
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)) ≫ m =
      (constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 * p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ) := by
  let q : (constantSheaf J (Type w)).obj (Λ × Λ) ⟶
      CoeffSet J Λ ⨯ CoeffSet J Λ :=
    prod.lift
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
      ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
  change q ≫ m = _
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ (CoeffSet J Λ).property
  ext T r
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  change m.hom.app T _ = _
  rw [hm]
  have hfst : (prod.fst : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.fst = _ from prod.lift_fst _ _)
  have hsnd : (prod.snd : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ).hom.app T
        (q.hom.app T ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)) =
      (((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
        (constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r) :=
    congrArg (fun f ↦ f.hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r))
        (show q ≫ prod.snd = _ from prod.lift_snd _ _)
  erw [hfst, hsnd]
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    types_comp_apply, constantMap_unit, id_eq]
  change (show ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.1))) *
    (show ((constantSheaf J CommRingCat.{w}).obj (CommRingCat.of Λ)).obj.obj T from
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      ((toSheafify J ((Functor.const Cᵒᵖ).obj Λ)).app T r.2))) =
    (((constantCommuteCompose J
      (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)).hom.app T
      (((constantSheaf J (Type w)).map
        (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1 * p.2))).hom.app T
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (Λ × Λ))).app T r)))
  rw [constantMap_unit, coeff_unit, coeff_unit, coeff_unit]
  exact (map_mul
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app T).hom) r.1 r.2).symm

private def coeffPair : (constantSheaf J (Type w)).obj (Λ × Λ) ⟶
    CoeffSet J Λ ⨯ CoeffSet J Λ :=
  prod.lift
    ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.1)) ≫
      (constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
    ((constantSheaf J (Type w)).map (TypeCat.ofHom (fun p : Λ × Λ ↦ p.2)) ≫
      (constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))

private instance coeffPair_isIso : IsIso (coeffPair J Λ) := by
  have h : coeffPair J Λ =
      (constantSheaf J (Type w)).map (Types.binaryProductIso Λ Λ).inv ≫
      prodComparison (constantSheaf J (Type w)) Λ Λ ≫
      prod.map ((constantCommuteCompose J
        (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
        ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)) := by
    apply prod.hom_ext
    · dsimp only [coeffPair]
      simp only [Category.assoc, prod.lift_fst]
      erw [prod.map_fst, prodComparison_fst_assoc, ← CategoryTheory.Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_fst]
    · dsimp only [coeffPair]
      simp only [Category.assoc, prod.lift_snd]
      erw [prod.map_snd, prodComparison_snd_assoc, ← CategoryTheory.Functor.map_comp_assoc,
        Types.binaryProductIso_inv_comp_snd]
  rw [h]
  have : PreservesFiniteLimits (constantSheaf J (Type w)) :=
    comp_preservesFiniteLimits _ _
  infer_instance

private theorem coeffPair_naturality :
    L.map (coeffPair J Λ) ≫ prodComparison L (CoeffSet J Λ) (CoeffSet J Λ) ≫
      prod.map
        (L.map ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).hom.app (CommRingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom)
        (L.map ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).hom.app (CommRingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom) =
      (constantComparison J K L R adj).hom.app (Λ × Λ) ≫ coeffPair K Λ := by
  apply prod.hom_ext
  all_goals
    simp only [Category.assoc, prod.map_fst, prod.map_snd,
      prodComparison_fst_assoc, prodComparison_snd_assoc,
      ← CategoryTheory.Functor.map_comp_assoc]
    dsimp only [coeffPair, normalizedRingComparison, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom]
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd, prod.lift_fst_assoc,
      prod.lift_snd_assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    rw [constantComparison_naturality_assoc]
    rfl

private theorem ringOperation_transport
    (m : CoeffSet J Λ ⨯ CoeffSet J Λ ⟶ CoeffSet J Λ)
    (m' : CoeffSet K Λ ⨯ CoeffSet K Λ ⟶ CoeffSet K Λ)
    (f : Λ × Λ → Λ)
    (hm : coeffPair J Λ ≫ m = (constantSheaf J (Type w)).map (TypeCat.ofHom f) ≫
      (constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ))
    (hm' : coeffPair K Λ ≫ m' = (constantSheaf K (Type w)).map (TypeCat.ofHom f) ≫
      (constantCommuteCompose K
        (CategoryTheory.forget CommRingCat.{w})).inv.app (CommRingCat.of Λ)) :
    inv (prodComparison L (CoeffSet J Λ) (CoeffSet J Λ)) ≫ L.map m ≫
        L.map ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).hom.app (CommRingCat.of Λ)) ≫
        (normalizedRingComparison J K L R adj Λ).hom =
      prod.map
        (L.map ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).hom.app (CommRingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom)
        (L.map ((constantCommuteCompose J
          (CategoryTheory.forget CommRingCat.{w})).hom.app (CommRingCat.of Λ)) ≫
          (normalizedRingComparison J K L R adj Λ).hom) ≫ m' := by
  apply (cancel_epi
    (L.map (coeffPair J Λ) ≫ prodComparison L (CoeffSet J Λ) (CoeffSet J Λ))).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  have h := congrArg (fun g ↦ g ≫ m') (coeffPair_naturality J K L R adj Λ)
  simp only [Category.assoc] at h
  rw [h]
  rw [hm']
  rw [← L.map_comp_assoc, hm]
  dsimp only [normalizedRingComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [constantComparison_naturality_assoc]
  rfl

end CoefficientConstruction

private noncomputable def constantRingSetComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [HasWeakSheafify JC CommRingCat.{w}] [HasWeakSheafify JD CommRingCat.{w}]
    (L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (kappa : constantSheaf JC (Type w) ⋙ L ≅ constantSheaf JD (Type w)) :
    (constantSheaf JC CommRingCat.{w} ⋙ sheafForget JC ⋙ L) ≅
      constantSheaf JD CommRingCat.{w} ⋙ sheafForget JD := by
    refine NatIso.ofComponents (fun A ↦ ?_) ?_
    · exact (L.mapIso ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).app A) ≪≫
        (kappa.app A) ≪≫
        (((constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).app A).symm))
    · intro A B f
      have hJ :=
        (constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.naturality f
      have hD :=
        (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.naturality f
      have hJ' : (sheafForget JC).map ((constantSheaf JC CommRingCat.{w}).map f) ≫
          (constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app B =
          (constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A ≫
            (constantSheaf JC (Type w)).map (CategoryTheory.forget CommRingCat.{w} |>.map f) := by
        simpa only [Functor.comp_map] using hJ
      have hD' : (constantSheaf JD (Type w)).map (CategoryTheory.forget CommRingCat.{w} |>.map f) ≫
          (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app B =
          (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app A ≫
            (sheafForget JD).map ((constantSheaf JD CommRingCat.{w}).map f) := by
        simpa only [Functor.comp_map] using hD
      have hk := kappa.hom.naturality ((CategoryTheory.forget CommRingCat.{w}).map f)
      have hk' :
          L.map ((constantSheaf JC (Type w)).map ((CategoryTheory.forget CommRingCat.{w}).map f)) ≫
          kappa.hom.app B = kappa.hom.app A ≫
            (constantSheaf JD (Type w)).map ((CategoryTheory.forget CommRingCat.{w}).map f) := by
        simpa only [Functor.comp_map] using hk
      dsimp
      rw [← Category.assoc, ← L.map_comp, hJ', L.map_comp]
      change L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
        L.map ((constantSheaf JC (Type w)).map ((CategoryTheory.forget CommRingCat.{w}).map f)) ≫
          kappa.hom.app B ≫ (constantCommuteCompose JD
            (CategoryTheory.forget CommRingCat.{w})).inv.app B = _
      calc
        _ = L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
            (L.map ((constantSheaf JC (Type w)).map
              ((CategoryTheory.forget CommRingCat.{w}).map f)) ≫
              kappa.hom.app B) ≫
            (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app B := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
            (kappa.hom.app A ≫
              (constantSheaf JD (Type w)).map ((CategoryTheory.forget CommRingCat.{w}).map f)) ≫
            (constantCommuteCompose JD
              (CategoryTheory.forget CommRingCat.{w})).inv.app B := by rw [hk']
        _ = L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantSheaf JD (Type w)).map ((CategoryTheory.forget CommRingCat.{w}).map f) ≫
              (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app B) := by
              simp only [Category.assoc]
        _ = L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
            kappa.hom.app A ≫
            ((constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app A ≫
              (sheafForget JD).map ((constantSheaf JD CommRingCat.{w}).map f)) := by rw [hD']
        _ = _ := by simp only [Category.assoc]

/-- Component formula for the normalized comparison; keeps its naturality proof opaque. -/
private theorem constantRingSetComparison_hom_app
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [HasWeakSheafify JC CommRingCat.{w}] [HasWeakSheafify JD CommRingCat.{w}]
    (L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (kappa : constantSheaf JC (Type w) ⋙ L ≅ constantSheaf JD (Type w))
    (A : CommRingCat.{w}) :
    (constantRingSetComparison JC JD L kappa).hom.app A =
      (L.mapIso ((constantCommuteCompose JC
          (CategoryTheory.forget CommRingCat.{w})).app A) ≪≫
        kappa.app A ≪≫ ((constantCommuteCompose JD
          (CategoryTheory.forget CommRingCat.{w})).app A).symm).hom := by
  rfl

private noncomputable def constantPointTerminal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] :
    IsTerminal ((constantSheaf J (Type w)).obj PUnit.{w + 1}) :=
  (Types.isTerminalPUnit.isTerminalObj (Functor.const Cᵒᵖ) _).isTerminalObj
    (presheafToSheaf J (Type w)) _

private theorem point_section
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] (U : Cᵒᵖ)
    (x : ((constantSheaf J (Type w)).obj PUnit.{w + 1}).obj.obj U) :
    x = (toSheafify J ((Functor.const Cᵒᵖ).obj PUnit.{w + 1})).app U PUnit.unit := by
  let : Unique (((constantSheaf J (Type w)).obj PUnit.{w + 1}).obj.obj U) :=
    Types.isTerminalEquivUnique _
      (((constantPointTerminal J).isTerminalObj (sheafToPresheaf J (Type w)) _).isTerminalObj
        ((CategoryTheory.evaluation Cᵒᵖ (Type w)).obj U) _)
  exact Subsingleton.elim _ _

private theorem section_coeff_unit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasWeakSheafify J CommRingCat.{w}] (A : CommRingCat.{w}) (U : Cᵒᵖ) (a : A) :
    ((constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).inv.app A).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type w))).app U a) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a := by
  have h := sheafComposeIso_hom_fac J
    (CategoryTheory.forget CommRingCat.{w}) ((Functor.const Cᵒᵖ).obj A)
  have hc := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ A (CategoryTheory.forget CommRingCat.{w})).inv
  change (((toSheafify J ((Functor.const Cᵒᵖ).obj (A : Type w))) ≫
    (sheafifyMap J (Functor.constComp Cᵒᵖ A (CategoryTheory.forget CommRingCat.{w})).inv) ≫
    (sheafifyComposeIso J
      (CategoryTheory.forget CommRingCat.{w}) ((Functor.const Cᵒᵖ).obj A)).hom).app U) a = _
  rw [← Category.assoc, ← hc, Category.assoc, h]
  rfl

private theorem section_constantMap_unit
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    (X Y : Type w) (f : X → Y) (U : Cᵒᵖ) (x : X) :
    ((constantSheaf J (Type w)).map (TypeCat.ofHom f)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).app U x) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj Y)).app U (f x) := by
  exact (congrArg (fun g ↦ g.app U x)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (TypeCat.ofHom f)))).symm

/-- The canonical comparison fixes sheafified constant sections.
Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(blueprint: lem-pur-coefficient-constant-ring-images). -/
private theorem canonicalConstantSectionComparison
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
    [HasWeakSheafify JC CommRingCat.{w}] [HasWeakSheafify JD CommRingCat.{w}]
    (L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (kappa : constantSheaf JC (Type w) ⋙ L ≅ constantSheaf JD (Type w)) :
      ∀ (a : CommRingCat.{w}) (x : a) (T : Sheaf JC (Type w))
        (s : T ⟶ (sheafCompose JC (CategoryTheory.forget CommRingCat.{w})).obj
          ((constantSheaf JC CommRingCat.{w}).obj a)),
        (∀ (U : Cᵒᵖ) (y : T.obj.obj U),
          (@id (((constantSheaf JC CommRingCat.{w}).obj a).obj.obj U) (s.hom.app U y)) =
            (toSheafify JC ((Functor.const Cᵒᵖ).obj a)).app U x) →
        ∀ (W : Dᵒᵖ) (z : (L.obj T).obj.obj W),
          (@id (((constantSheaf JD CommRingCat.{w}).obj a).obj.obj W)
            ((constantRingSetComparison.{w} JC JD L kappa).hom.app a |>.hom.app W
              ((L.map s).hom.app W z))) =
            (toSheafify JD ((Functor.const Dᵒᵖ).obj a)).app W x := by
  intro A a T s hs W y
  let f : PUnit.{w + 1} ⟶ (A : Type w) := TypeCat.ofHom (fun _ ↦ a)
  let t : T ⟶ (constantSheaf JC (Type w)).obj PUnit.{w + 1} :=
    (constantPointTerminal.{w} JC).from T
  have hs' : s = t ≫ (constantSheaf JC (Type w)).map f ≫
      (constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).inv.app A := by
    apply Sheaf.hom_ext
    ext U x
    change s.hom.app U x = _
    have hx := hs U x
    dsimp only [id_eq] at hx
    rw [hx]
    change _ = ((constantCommuteCompose JC
      (CategoryTheory.forget CommRingCat.{w})).inv.app A).hom.app U
      (((constantSheaf JC (Type w)).map f).hom.app U (t.hom.app U x))
    erw [point_section.{w} JC U (t.hom.app U x), section_constantMap_unit, section_coeff_unit]
  have hn := kappa.hom.naturality f
  have hn' : L.map ((constantSheaf JC (Type w)).map f) ≫ kappa.hom.app A =
      kappa.hom.app PUnit.{w + 1} ≫ (constantSheaf JD (Type w)).map f := by
    simpa only [Functor.comp_map] using hn
  have heq : L.map s ≫ (constantRingSetComparison.{w} JC JD L kappa).hom.app A =
      L.map t ≫ kappa.hom.app PUnit.{w + 1} ≫
        (constantSheaf JD (Type w)).map f ≫
          (constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app A := by
    rw [hs']
    change L.map (t ≫ (constantSheaf JC (Type w)).map f ≫
      (constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).inv.app A) ≫
      (L.map ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A) ≫
        kappa.hom.app A ≫ (constantCommuteCompose JD
          (CategoryTheory.forget CommRingCat.{w})).inv.app A) = _
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← L.map_comp_assoc
      ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).inv.app A)
      ((constantCommuteCompose JC (CategoryTheory.forget CommRingCat.{w})).hom.app A),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun g ↦ L.map t ≫ g ≫ (constantCommuteCompose JD
        (CategoryTheory.forget CommRingCat.{w})).inv.app A) hn'
  change (L.map s ≫ (constantRingSetComparison.{w} JC JD L kappa).hom.app A).hom.app W y = _
  rw [heq]
  change ((constantCommuteCompose JD (CategoryTheory.forget CommRingCat.{w})).inv.app A).hom.app W
    (((constantSheaf JD (Type w)).map f).hom.app W
      ((kappa.hom.app PUnit.{w + 1}).hom.app W ((L.map t).hom.app W y))) = _
  erw [point_section.{w} JD W
    ((kappa.hom.app PUnit.{w + 1}).hom.app W ((L.map t).hom.app W y)),
    section_constantMap_unit, section_coeff_unit]

open SheafOfModules.GeometricConstruction in
private theorem ringTransport_algebraic
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{w}) (S : Sheaf K CommRingCat.{w})
    (d : SheafOfModules.RingInverseImage L R S) :
    ∃ a : SheafOfModules.AlgebraicInverseImage L R S,
      a.ringUnderlying = d.ringUnderlying := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let e := d.ringUnderlying
  have hadd : L.map (ringAdd R) ≫ e.hom =
      CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ ringAdd S := by
    ext U x
    exact d.ringAdd _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringAdd R) (fun _ _ ↦ rfl) U x
  have hmul : L.map (ringMul R) ≫ e.hom =
      CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ ringMul S := by
    ext U x
    exact d.ringMul _ (CartesianMonoidalCategory.fst _ _)
      (CartesianMonoidalCategory.snd _ _) (ringMul R) (fun _ _ ↦ rfl) U x
  have transport (a : rset R ⊗ rset R ⟶ rset R)
      (b : rset S ⊗ rset S ⟶ rset S)
      (h : L.map a ≫ e.hom = CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ b) :
      b ≫ e.inv = (e.inv ⊗ₘ e.inv) ≫ Functor.LaxMonoidal.μ L _ _ ≫ L.map a := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    rw [h]
    simp only [← Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
      Functor.Monoidal.μ_δ_assoc]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, e.inv_hom_id,
      id_tensorHom_id, Category.id_comp]
  have ha := transport (ringAdd R) (ringAdd S) hadd
  have hm := ringIso_isMonHom L R S e.symm (transport (ringMul R) (ringMul S) hmul)
  let F := imageFunctor L R S e.inv ha hm
  refine ⟨{
    ringUnderlying := e
    ringAdd := d.ringAdd
    ringMul := d.ringMul
    ringZero := d.ringZero
    ringOne := d.ringOne
    modules := F
    moduleUnderlying := imageFunctorUnderlying L R S e.inv ha hm
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }, rfl⟩
  · intro M T a b t ht V x
    have he : t = CartesianMonoidalCategory.lift a b ≫ addition R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    rfl
  · intro M T a ht V x
    have he : a = CartesianMonoidalCategory.toUnit T ≫
        MonObj.one (X := (additiveObject R M).X) := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.toUnit_ε]
    rfl
  · intro M T a b t ht V x
    change (L.map t).hom.app V x = (imageAction L R S e.inv M).hom.app V
      (e.hom.hom.app V ((L.map a).hom.app V x), (L.map b).hom.app V x)
    have he : t = CartesianMonoidalCategory.lift a b ≫ action R M := by
      ext U y
      exact ht U y
    rw [he, L.map_comp, ← Functor.Monoidal.lift_μ]
    change (L.map (action R M)).hom.app V
      ((Functor.LaxMonoidal.μ L _ _).hom.app V
        ((L.map a).hom.app V x, (L.map b).hom.app V x)) =
      (L.map (action R M)).hom.app V
        ((Functor.LaxMonoidal.μ L _ _).hom.app V
          (e.inv.hom.app V (e.hom.hom.app V ((L.map a).hom.app V x)),
            (L.map b).hom.app V x))
    rw [show e.inv.hom.app V (e.hom.hom.app V ((L.map a).hom.app V x)) =
      (L.map a).hom.app V x from
        congrArg (fun f ↦ f.hom.app V ((L.map a).hom.app V x)) e.hom_inv_id]

section Existence
open SheafOfModules.GeometricConstruction CategoryTheory.MonoidalCategory
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify K CommRingCat.{w}]
  [J.PreservesSheafification (CategoryTheory.forget CommRingCat.{w})]
  [K.PreservesSheafification (CategoryTheory.forget CommRingCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
  [PreservesFiniteLimits L]

include V adj in
private theorem constantRingLift (A : CommRingCat.{w}) :
    ∃ I : AlgebraicInverseImage L ((constantSheaf J CommRingCat.{w}).obj A)
        ((constantSheaf K CommRingCat.{w}).obj A),
      I.ringUnderlying =
        (constantRingSetComparison.{w} J K L (constantComparison J K L V adj)).app A := by
  let : L.Braided := Functor.Braided.ofChosenFiniteProducts L
  let R := (constantSheaf J CommRingCat.{w}).obj A
  let S := (constantSheaf K CommRingCat.{w}).obj A
  let e := (constantRingSetComparison.{w} J K L (constantComparison J K L V adj)).app A
  have hbinary (a : rset R ⊗ rset R ⟶ rset R)
      (b : rset S ⊗ rset S ⟶ rset S) (f : A × A → A)
      (ha : coeffPair J A ≫ (fromProd _ _ ≫ a) =
        (constantSheaf J (Type w)).map (TypeCat.ofHom f) ≫
          (constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).inv.app A)
      (hb : coeffPair K A ≫ (fromProd _ _ ≫ b) =
        (constantSheaf K (Type w)).map (TypeCat.ofHom f) ≫
          (constantCommuteCompose K (CategoryTheory.forget CommRingCat.{w})).inv.app A) :
      L.map a ≫ e.hom = CartesianMonoidalCategory.prodComparison L _ _ ≫
        (e.hom ⊗ₘ e.hom) ≫ b := by
    have h := ringOperation_transport J K L V adj A
      (fromProd _ _ ≫ a) (fromProd _ _ ≫ b) f ha hb
    have h' : L.map (fromProd _ _ ≫ a) =
        prodComparison L _ _ ≫ prod.map e.hom e.hom ≫ fromProd _ _ ≫ b ≫ e.inv := by
      apply (cancel_mono e.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      apply (cancel_epi (inv (prodComparison L (rset R) (rset R)))).mp
      change inv (prodComparison L (rset R) (rset R)) ≫
        L.map (fromProd _ _ ≫ a) ≫ e.hom =
          prod.map e.hom e.hom ≫ fromProd _ _ ≫ b at h
      change _ = inv (prodComparison L (rset R) (rset R)) ≫
        prodComparison L (rset R) (rset R) ≫ prod.map e.hom e.hom ≫ fromProd _ _ ≫ b
      rw [IsIso.inv_hom_id_assoc]
      exact h
    exact binary_inverse L _ _ e.symm a b ((binary_transport_iff L _ _ e.symm a b).1 h')
  have hadd := hbinary (ringAdd R) (ringAdd S) (fun p ↦ p.1 + p.2)
    (ringAddition_constants J A _ (fun _ _ ↦ rfl))
    (ringAddition_constants K A _ (fun _ _ ↦ rfl))
  have hmul := hbinary (ringMul R) (ringMul S) (fun p ↦ p.1 * p.2)
    (ringMultiplication_constants J A _ (fun _ _ ↦ rfl))
    (ringMultiplication_constants K A _ (fun _ _ ↦ rfl))
  let d : RingInverseImage L R S := {
    ringUnderlying := e
    ringAdd := by
      intro T a b t ht W x
      have h : t = CartesianMonoidalCategory.lift a b ≫ ringAdd R := by
        ext U y
        exact ht U y
      exact congrArg (fun f ↦ f.hom.app W x)
        (CategoryTheory.ConstantCompletion.transport_binary L e.hom _ _ hadd a b t h)
    ringMul := by
      intro T a b t ht W x
      have h : t = CartesianMonoidalCategory.lift a b ≫ ringMul R := by
        ext U y
        exact ht U y
      exact congrArg (fun f ↦ f.hom.app W x)
        (CategoryTheory.ConstantCompletion.transport_binary L e.hom _ _ hmul a b t h)
    ringZero := by
      intro T a ha W x
      have h := canonicalConstantSectionComparison.{w} J K L
        (constantComparison J K L V adj) A 0 T a (by
          intro U y
          simpa only [map_zero] using ha U y) W x
      simp only [map_zero] at h
      convert h using 1
      rfl
    ringOne := by
      intro T a ha W x
      have h := canonicalConstantSectionComparison.{w} J K L
        (constantComparison J K L V adj) A 1 T a (by
          intro U y
          simpa only [map_one] using ha U y) W x
      simp only [map_one] at h
      convert h using 1
      rfl }
  exact ringTransport_algebraic L R S d

include V adj in
/-- Constant rings have algebraic inverse images normalized by one natural comparison
on all constant sets. Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-coefficient-constant-ring-images).

Proof: identify global sections with maps from the constant singleton, and use the
set adjunction and preservation of the terminal object to compare global sections.
Uniqueness of left adjoints gives the natural comparison on constant sets. After
conjugating by the constant-sheaf forgetful comparisons, addition and multiplication
are preserved: precompose by the isomorphism from the constant sheaf on pairs, where
this is naturality for the two operations on the coefficient ring. Zero and one are
constant sections. Transport module operations with the finite-product comparisons;
the operation identities give an algebraic inverse-image presentation. -/
theorem coefficientConstantRingImages :
    ∃ kappa : constantSheaf J (Type w) ⋙ L ≅ constantSheaf K (Type w),
      ∀ A : CommRingCat.{w},
      ∃ I : AlgebraicInverseImage L ((constantSheaf J CommRingCat.{w}).obj A)
          ((constantSheaf K CommRingCat.{w}).obj A),
        I.ringUnderlying =
          L.mapIso ((constantCommuteCompose J (CategoryTheory.forget CommRingCat.{w})).app A) ≪≫
            kappa.app A ≪≫ ((constantCommuteCompose K
              (CategoryTheory.forget CommRingCat.{w})).app A).symm := by
  exact ⟨constantComparison J K L V adj, constantRingLift J K L V adj⟩

end Existence
end SheafOfModules.CoefficientConstantImages
