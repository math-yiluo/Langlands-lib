/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Normalized tensor comparison with independent site universes

Source: Stacks Project, Modules on Sites, Tag 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe uC vC u v w uD vD uT vT uB vB r a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite
open scoped ChangeOfRings
namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The section formula for the scalar-extension unit, using the existing tensor
sheafification. The equality identifies the supplied presentation of the extension object.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes). -/
def scalarLocalizationUnitSectionsOfUniverses
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (e : N = SheafOfModules.changeOfRingsOfUniverses φ M)
    (η : M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj N) : Prop :=
  ∀ (V : Cᵒᵖ) (x : M.val.obj V),
    (η ≫ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map (eqToHom e)).val.app V x =
      (toSheafify J (SheafOfModules.changeOfRingsPresheafOfUniverses φ M).presheaf).app V
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)

end CategoryTheory

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R S : Sheaf J CommRingCat.{u}}

attribute [local instance] cochainModulesMonoidal

private def restrictedTensorPresheafIsoAux (φ : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
      (unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))).val ⊗ M.val ≅
      (PresheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj
          (changeOfRingsPresheafOfUniverses.{vC, uC, u, u} φ M) := by
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
              (M.val.obj W)) :=
        inferInstanceAs (Module (R.obj.obj W) (M.val.obj W))
      change S.obj.map f s ⊗ₜ[R.obj.obj W, (φ.hom.app W).hom] M.val.map f m =
        changeOfRingsMapOfUniverses φ M f (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
      exact (changeOfRingsMap_tmulOfUniverses φ M f s m).symm

section
variable {R₀ B₀ : Sheaf J RingCat.{u}}

private noncomputable def restrictionSheafificationComparisonAux
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    (PresheafOfModules.sheafification (𝟙 R₀.obj)).obj
      ((PresheafOfModules.restrictScalars α.hom).obj P) ⟶
        (restrictScalars α).obj
          ((PresheafOfModules.sheafification (𝟙 B₀.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R₀.obj)).symm
    ((PresheafOfModules.restrictScalars α.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P))

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem restrictionSheafificationComparison_isIsoAux
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj) :
    IsIso (restrictionSheafificationComparisonAux α P) := by
  rw [← isIso_iff_of_reflects_iso _ (toSheaf R₀)]
  have he : (toSheaf R₀).map (restrictionSheafificationComparisonAux α P) = 𝟙 _ := by
    unfold restrictionSheafificationComparisonAux
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply ((CategoryTheory.sheafificationAdjunction
      J AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    change (PresheafOfModules.toPresheaf B₀.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app P) =
        CategoryTheory.toSheafify J P.presheaf
    exact PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _
  rw [he]
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem restrictionSheafificationComparison_unitAux
    (α : R₀ ⟶ B₀) (P : PresheafOfModules.{u} B₀.obj)
    (W : Cᵒᵖ) (x : P.obj W) :
    (restrictionSheafificationComparisonAux α P).val.app W
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

attribute [local irreducible] restrictionSheafificationComparisonAux

/-- The canonical map from the presheaf tensor to the underlying sheaf tensor.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes). -/
def scalarTelescopeTensorUnitOfUniverses
    (M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    M.val ⊗ N.val ⟶ ((cochainModulesMonoidal R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app _ ≫
      (tensorObjIsoSheafification M N).inv.val

set_option maxHeartbeats 50000 in
-- Mixed tensor coefficient structures require additional elaboration.
/-- Restricted extension of scalars is tensoring with the restricted target ring.
Source: Stacks Project, Modules on Sites, Tag 03EK.
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes).

Proof: the presheaf tensor of the restricted target ring with M has exactly the
same section modules as restricted sectionwise scalar extension. Both restriction
maps send s tensor m to the tensor of the two restrictions, so the identity maps
form an isomorphism. Sheafify it over R. Restriction commutes with sheafification:
after forgetting to abelian sheaves the comparison is the identity of the same
sheafification, and forgetting reflects isomorphisms. Compose with the canonical
tensor-sheafification comparison. Naturality of the sheafification unit gives the
pure-tensor formula. No flatness or localization assumption is used. -/
theorem exists_scalarTelescopeTensorComparisonOfUniverses (φ : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (cochainModulesMonoidal R).tensorObj
        ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M ≅
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (changeOfRingsOfUniverses.{vC, uC, u, u} φ M),
      ∀ (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
        e.hom.val.app V
          ((scalarTelescopeTensorUnitOfUniverses
            ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
              (unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))) M).app V
            ((show ((restrictScalars.{u}
                ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
                  (unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
                    S))).val.obj V
              from s) ⊗ₜ[R.obj.obj V] m)) =
        (toSheafify J (changeOfRingsPresheafOfUniverses.{vC, uC, u, u} φ M).presheaf).app V
          (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m) := by
  let N := (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
    (unit.{vC, uC, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  let P := changeOfRingsPresheafOfUniverses.{vC, uC, u, u} φ M
  let SR := PresheafOfModules.sheafification.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let eP := restrictedTensorPresheafIsoAux φ M
  have := restrictionSheafificationComparison_isIsoAux
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P
  let e := tensorObjIsoSheafification N M ≪≫ SR.mapIso eP ≪≫
    asIso (restrictionSheafificationComparisonAux
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P)
  have he : (tensorObjIsoSheafification N M).inv ≫ e.hom =
      SR.map eP.hom ≫ restrictionSheafificationComparisonAux
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P := by
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    simp only [Iso.inv_hom_id_assoc]
  clear_value e
  refine ⟨e, ?_⟩
  intro V s m
  have hn := adj.unit.naturality eP.hom
  have hn' := congrArg (fun k ↦ (k.app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) hn
  have hr' := restrictionSheafificationComparison_unitAux
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)
  change ((scalarTelescopeTensorUnitOfUniverses N M ≫ e.hom.val).app V)
    ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m) = _
  unfold scalarTelescopeTensorUnitOfUniverses
  rw [Category.assoc]
  change ((adj.unit.app (N.val ⊗ M.val) ≫
    ((tensorObjIsoSheafification N M).inv ≫ e.hom).val).app V) _ = _
  rw [he]
  change (restrictionSheafificationComparisonAux
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V
    ((SR.map eP.hom).val.app V
      ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m))) = _
  change (adj.unit.app ((PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ).hom).obj P)).app V
        (eP.hom.app V ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) =
      (SR.map eP.hom).val.app V ((adj.unit.app (N.val ⊗ M.val)).app V
        ((show N.val.obj V from s) ⊗ₜ[R.obj.obj V] m)) at hn'
  exact (congrArg ((restrictionSheafificationComparisonAux
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) P).val.app V) hn'.symm).trans hr'

/-- A concrete tensor-unit isomorphism, normalized on every local pure tensor.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes). -/
def scalarTelescopeRegularTensorIsoOfUniverses
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (cochainModulesMonoidal R).tensorObj
      (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) M ≅ M :=
  tensorObjIsoSheafification _ M ≪≫
    (PresheafOfModules.sheafification
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit).app M

private lemma whiskerRight_tensorObjIsoSheafification_homAux {A A' : SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : A' ⟶ A) (T : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫ (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (((sheafCompose J (forget₂
    CommRingCat RingCat)).obj R)).obj)).counit.naturality f
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

/-- Pure tensor sections commute with maps of the first factor.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes). -/
theorem scalarTelescopeTensorUnit_naturalityOfUniverses
    {L L' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : L ⟶ L')
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    scalarTelescopeTensorUnitOfUniverses L M ≫ (f ▷ M).val =
      (f.val ▷ M.val) ≫ scalarTelescopeTensorUnitOfUniverses L' M := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have h : (tensorObjIsoSheafification L M).inv ≫ f ▷ M =
      (PresheafOfModules.sheafification
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).map
          (f.val ▷ M.val) ≫ (tensorObjIsoSheafification L' M).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← whiskerRight_tensorObjIsoSheafification_homAux,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  unfold scalarTelescopeTensorUnitOfUniverses
  rw [Category.assoc, ← comp_val, h, comp_val, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ (tensorObjIsoSheafification L' M).inv.val)
    (adj.unit.naturality (f.val ▷ M.val)).symm

set_option maxHeartbeats 50000 in
-- Elaborating the tensor unitor requires additional coefficient comparisons.
/-- The inverse regular tensor unitor sends a section to the local tensor of one with it.
Source: Stacks Project, Tag 03EK
(blueprint: lem-weil-pbc-scalar-localization-tensor-comparison-of-universes). -/
theorem scalarTelescopeRegularTensorIso_inv_applyOfUniverses
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (scalarTelescopeRegularTensorIsoOfUniverses M).inv.val.app V x =
      (scalarTelescopeTensorUnitOfUniverses (unit ((sheafCompose J (forget₂ CommRingCat
        RingCat)).obj R)) M).app V
        ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  have : IsIso adj.counit := by dsimp [adj]; infer_instance
  let e := (asIso adj.counit).app M
  let f := (SheafOfModules.forget _).mapIso e
  have hc : e.inv.val = adj.unit.app M.val := by
    apply (cancel_mono f.hom).1
    change e.inv.val ≫ e.hom.val = adj.unit.app M.val ≫ e.hom.val
    have h := adj.right_triangle_components M
    have hi := congrArg SheafOfModules.Hom.val e.inv_hom_id
    exact hi.trans h.symm
  have hn := adj.unit.naturality (λ_ M.val).inv
  have h := congrArg (fun f ↦ f.app V x) hn
  simp only [scalarTelescopeRegularTensorIsoOfUniverses, Iso.trans_inv, Functor.mapIso_inv,
    comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [hc]
  simp only [Functor.id_map, Functor.comp_map,
    PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  erw [← h]
  rfl

end SheafOfModules
