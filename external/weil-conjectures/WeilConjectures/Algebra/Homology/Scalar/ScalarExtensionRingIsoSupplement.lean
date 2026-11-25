/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso

/-!
# Scalar extension along an isomorphism of ring sheaves

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).

The transported module functor is the existing restriction of scalars along the inverse.
The tensor convention in the existing change-of-rings construction puts the scalar first:
`s ⊗ x` represents the node's `x ⊗ s` under tensor symmetry.
-/

@[expose] public section

universe uC vC r m

open CategoryTheory
open scoped ChangeOfRings

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false

private theorem scalarIso_inv_hom
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) (U : Cᵒᵖ) (x : R.obj.obj U) :
    c.inv.hom.app U (c.hom.hom.app U x) = x := by
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) c.hom_inv_id) x

private theorem scalarIso_hom_inv
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{r}} (c : R ≅ S) (U : Cᵒᵖ) (x : S.obj.obj U) :
    c.hom.hom.app U (c.inv.hom.app U x) = x := by
  exact ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) c.inv_hom_id) x

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  {R S : Sheaf J CommRingCat.{r}}

private noncomputable def scalarIsoSectionHom (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) :
    (changeOfRingsPresheafOfUniverses c.hom M).obj U ⟶
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M).val.obj U :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (c.hom.hom.app U).hom
    (ModuleCat.ofHom (X := M.val.obj U)
      (Y := (ModuleCat.restrictScalars (c.hom.hom.app U).hom).obj
        (((restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M).val.obj U))
      { toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro a x
          change a • x = c.inv.hom.app U (c.hom.hom.app U a) • x
          rw [scalarIso_inv_hom] })

private theorem scalarIsoSectionHom_tmul (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    scalarIsoSectionHom c M U (s ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x) =
      c.inv.hom.app U s • x := by
  rfl

private noncomputable def scalarIsoSectionInv (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (U : Cᵒᵖ) :
    ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M).val.obj U ⟶
      (changeOfRingsPresheafOfUniverses c.hom M).obj U :=
  ModuleCat.ofHom
    (X := ((restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M).val.obj U)
    (Y := (changeOfRingsPresheafOfUniverses c.hom M).obj U)
    { toFun := fun x ↦ (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom]
        (show M.val.obj U from x)
      map_add' := by intros; apply TensorProduct.tmul_add
      map_smul' := by
        intro s x
        change S.obj.obj U at s
        change M.val.obj U at x
        let : Module (R.obj.obj U) (S.obj.obj U) :=
          Module.compHom (S.obj.obj U) (c.hom.hom.app U).hom
        change (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom]
          (c.inv.hom.app U s • x) =
          s • (show (changeOfRingsPresheafOfUniverses c.hom M).obj U from
            (1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)
        rw [TensorProduct.tmul_smul]
        change (c.hom.hom.app U (c.inv.hom.app U s) * 1) ⊗ₜ[R.obj.obj U,
          (c.hom.hom.app U).hom] x =
          (s * 1) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x
        rw [scalarIso_hom_inv] }

private noncomputable def scalarIsoPresheaf (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsPresheafOfUniverses c.hom M ≅
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M).val :=
  PresheafOfModules.isoMk (fun U ↦
    { hom := scalarIsoSectionHom c M U
      inv := scalarIsoSectionInv c M U
      hom_inv_id := by
        apply ModuleCat.ExtendScalars.hom_ext
        intro x
        change scalarIsoSectionInv c M U
          (scalarIsoSectionHom c M U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)) = _
        rw [scalarIsoSectionHom_tmul, map_one, one_smul]
        rfl
      inv_hom_id := by
        ext x
        change scalarIsoSectionHom c M U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom]
            (show M.val.obj U from x)) = x
        rw [scalarIsoSectionHom_tmul, map_one, one_smul] }) (by
    intro U V f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change scalarIsoSectionHom c M V (changeOfRingsMapOfUniverses c.hom M f
      ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)) =
      M.val.map f (scalarIsoSectionHom c M U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x))
    rw [changeOfRingsMap_tmulOfUniverses, map_one, scalarIsoSectionHom_tmul,
      scalarIsoSectionHom_tmul, map_one, map_one, one_smul, one_smul])

private def isoFromAdjunction {D E : Type*} [Category D] [Category E]
    {L : D ⥤ E} {G : E ⥤ D} [G.Faithful] (adj : L ⊣ G)
    {P : D} {T : E} (e : P ≅ G.obj T) (a : L.obj P ⟶ T) (b : T ⟶ L.obj P)
    (ha : adj.homEquiv P T a = e.hom)
    (hb : G.map b = e.inv ≫ adj.unit.app P) : L.obj P ≅ T where
  hom := a
  inv := b
  hom_inv_id := by
    apply (adj.homEquiv P (L.obj P)).injective
    rw [adj.homEquiv_naturality_right, ha, hb, ← Category.assoc,
      e.hom_inv_id, Category.id_comp, adj.homEquiv_id]
  inv_hom_id := by
    apply G.map_injective
    rw [G.map_comp, hb, Category.assoc, ← adj.homEquiv_unit, ha,
      e.inv_hom_id, G.map_id]

private noncomputable def scalarIsoSheaf (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    changeOfRingsOfUniverses c.hom M ≅
      (restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M := by
  let T := (restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M
  let e := scalarIsoPresheaf c M
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)
  let a := (adj.homEquiv (changeOfRingsPresheafOfUniverses c.hom M) T).symm e.hom
  exact isoFromAdjunction adj e a ⟨e.inv ≫ adj.unit.app _⟩
    ((adj.homEquiv (changeOfRingsPresheafOfUniverses c.hom M) T).apply_symm_apply e.hom)
    rfl

private theorem scalarIsoSheaf_unit (c : R ≅ S)
    (M : ringedSiteModules.{max r m}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
        (changeOfRingsPresheafOfUniverses c.hom M) ≫ (scalarIsoSheaf c M).hom.val =
      (scalarIsoPresheaf c M).hom := by
  exact ((PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).homEquiv
      (changeOfRingsPresheafOfUniverses c.hom M)
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M)).apply_symm_apply
          (scalarIsoPresheaf c M).hom

/-- Scalar extension along a ring-sheaf isomorphism is naturally the original abelian
sheaf with action transported along its inverse, with both specified section formulas.
Source: Stacks, Tags 03CZ, 03EK and 03CY
(blueprint: lem-weil-sheaf-scalar-extension-ring-iso).

Proof: (1) restriction of scalars along `c.inv` retains the abelian sheaf and all maps;
its action is `s • x = c.inv(s) • x`, compatible with restrictions by naturality of
`c.inv` (situation-conventions). (2) The balanced map on local tensors
sends `s ⊗ x` to `c.inv(s) • x`; the tensor universal property makes it linear
(def-weil-pbc-module-tensor-product). (3) The maps commute with restrictions since
`c.inv` is natural (def-pur-sheaf-tensor-product). (4) The inverse before sheafification
sends `x` to `1 ⊗ x`; balancing and the inverse identities of `c` show that both
composites are identities, first on pure tensors and then by tensor generation.
(5) The module-sheafification universal property extends the forward map uniquely;
compose the inverse with the unit. One inverse identity holds directly, and the other
follows by uniqueness after precomposition with the unit
(def-weil-presheaf-modules-sheafification). These give the two displayed formulas.
(6) For `h : M ⟶ N`, both naturality composites take `s ⊗ x` to
`c.inv(s) • h(x) = h(c.inv(s) • x)`. Tensor generation and the same sheafification
uniqueness give naturality, without assuming sections of a sheafified tensor are pure. -/
theorem exists_scalarExtensionRingIso (c : R ≅ S) :
    ∃ theta : ∀ M : ringedSiteModules.{max r m}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R),
      changeOfRingsOfUniverses c.hom M ≅
        (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M,
      (∀ (M : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U),
        (theta M).hom.val.app U (scalarExtensionRingIsoTmul c.hom M U x s) =
          (c.inv.hom.app U) s • x) ∧
      (∀ (M : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        (U : Cᵒᵖ) (x : M.val.obj U),
        (theta M).inv.val.app U x = scalarExtensionRingIsoTmul c.hom M U x 1) ∧
      (∀ (M N : ringedSiteModules.{max r m}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (h : M ⟶ N),
        changeOfRingsHomOfUniverses c.hom M h ≫ (theta N).hom =
          (theta M).hom ≫
            (restrictScalars
              ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).map h) := by
  refine ⟨scalarIsoSheaf c, ?_, ?_, ?_⟩
  · intro M U x s
    have h := congrArg (fun f ↦ f.app U) (scalarIsoSheaf_unit c M)
    exact (ConcreteCategory.congr_hom h
      (s ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)).trans
        (scalarIsoSectionHom_tmul c M U x s)
  · intro M U x
    rfl
  · intro M N h
    let A := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S
    let adj := PresheafOfModules.sheafificationAdjunction (R := A) (𝟙 _)
    apply (adj.homEquiv (changeOfRingsPresheafOfUniverses c.hom M)
      ((restrictScalars
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj N)).injective
    have hM : adj.homEquiv (changeOfRingsPresheafOfUniverses c.hom M)
        ((restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M)
          (scalarIsoSheaf c M).hom = (scalarIsoPresheaf c M).hom :=
      scalarIsoSheaf_unit c M
    have hN : adj.homEquiv (changeOfRingsPresheafOfUniverses c.hom N)
        ((restrictScalars
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj N)
          (scalarIsoSheaf c N).hom = (scalarIsoPresheaf c N).hom :=
      scalarIsoSheaf_unit c N
    change adj.homEquiv _ _
      ((PresheafOfModules.sheafification (R := A) (𝟙 _)).map
        ({ app := fun U ↦ (ModuleCat.extendScalars (c.hom.hom.app U).hom).map (h.val.app U)
           naturality := changeOfRingsHom_naturalityOfUniverses c.hom M h } :
          changeOfRingsPresheafOfUniverses c.hom M ⟶
            changeOfRingsPresheafOfUniverses c.hom N) ≫
        (scalarIsoSheaf c N).hom) = _
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, hN, hM]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change scalarIsoSectionHom c N U
      ((ModuleCat.extendScalars (c.hom.hom.app U).hom).map (h.val.app U)
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x)) =
      h.val.app U (scalarIsoSectionHom c M U
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (c.hom.hom.app U).hom] x))
    rw [ModuleCat.ExtendScalars.map_tmul, scalarIsoSectionHom_tmul,
      scalarIsoSectionHom_tmul, map_one, one_smul, one_smul]
    rfl

end SheafOfModules
