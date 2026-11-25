/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Invertibility of the pushout tensor comparison

Source: Stacks Project, Tags 01SB and 008A.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-comparison-is-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped ChangeOfRings TensorProduct

namespace SheafOfModules

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {T : TopCat.{u}} {D C A B : T.Sheaf CommRingCat.{u}}

set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).obj E
set_option hygiene false in
local notation "𝓻" a =>
  (sheafCompose (Opens.grothendieckTopology T) (forget₂ CommRingCat.{u} RingCat.{u})).map a
private theorem stalkPushout (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (hp : IsPushout r s b t) (x : T) :
    IsPushout ((TopCat.Presheaf.stalkFunctor CommRingCat x).map r.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map s.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map b.hom)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map t.hom) := by
  let F := TopCat.Sheaf.forget CommRingCat T ⋙ TopCat.Presheaf.stalkFunctor CommRingCat x
  have : PreservesColimits F := inferInstance
  exact hp.map F

private theorem stalkRestrict_smul (s : D ⟶ A)
    (M : SheafOfModules.{u} (𝓡 A)) (x : T)
    (d : TopCat.Presheaf.stalk (C := CommRingCat.{u}) D.obj x)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :
    d • (show TopCat.Presheaf.stalk (C := Ab.{u})
      ((restrictScalars (𝓻 s)).obj M).val.presheaf x from m) =
    (show TopCat.Presheaf.stalk (C := CommRingCat.{u}) A.obj x from
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map s.hom) d) • m := by
  obtain ⟨U, hxU, d, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := CommRingCat.{u}) D.obj d
  obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← TopCat.Presheaf.germ_res_apply D.obj
    (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx d,
    ← TopCat.Presheaf.germ_res_apply M.val.presheaf
      (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  rw [← PresheafOfModules.germ_smul]
  exact (PresheafOfModules.germ_smul ((restrictScalars (𝓻 s)).obj M).val x
    (U ⊓ V) hx (D.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op d)
    (M.val.presheaf.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op m)).symm

set_option hygiene false in
local notation "θ" a:arg M:arg =>
  (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 _).obj)).unit.app
    (changeOfRingsPresheaf.{u, u, u} a M)

private theorem comparison_formula (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (M : SheafOfModules.{u} (𝓡 A))
    (f : changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) ⟶
      (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M))
    (hf : ∀ (W : (Opens T)ᵒᵖ) (m : M.val.obj W),
      f.val.app W ((θ r((restrictScalars (𝓻 s)).obj M)).app W
        ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
      (θ t M).app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m))
    (W : (Opens T)ᵒᵖ) (c : C.obj.obj W) (m : M.val.obj W) :
    f.val.app W ((θ r((restrictScalars (𝓻 s)).obj M)).app W
      (c ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
    (θ t M).app W ((b.hom.app W c) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m) := by
  have hr : (θ r((restrictScalars (𝓻 s)).obj M)).app W
      (c ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m) =
      c • (show (changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M)).val.obj W from
        (θ r((restrictScalars (𝓻 s)).obj M)).app W
          ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) := by
    rw [← ((θ r((restrictScalars (𝓻 s)).obj M)).app W).hom.map_smul]
    congr 1
    change _ = c • ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom]
      (show ((restrictScalars (𝓻 s)).obj M).val.obj W from m))
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [hr, (f.val.app W).hom.map_smul, hf]
  change b.hom.app W c • (show (changeOfRings.{u, u, u} t M).val.obj W from
    (θ t M).app W ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m)) = _
  rw [← ((θ t M).app W).hom.map_smul]
  congr 1
  change (b.hom.app W c) •
    ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m) = _
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]

open TopCat.Presheaf in
private theorem stalkTensor_addHom_ext (r : D ⟶ C)
    (M : SheafOfModules.{u} (𝓡 D)) (x : T) {N : Type u} [AddCommGroup N]
    (g h : (ModuleCat.extendScalars
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map r.hom).hom).obj
          (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u}) D.obj x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x)) →+ N)
    (hgh : ∀ (U : Opens T) (hx : x ∈ U) (c : C.obj.obj (Opposite.op U))
        (m : M.val.obj (Opposite.op U)),
      g (TopCat.Presheaf.germ C.obj U x hx c
          ⊗ₜ[stalk (C := CommRingCat) D.obj x,((stalkFunctor CommRingCat x).map r.hom).hom]
          TopCat.Presheaf.germ M.val.presheaf U x hx m) =
      h (TopCat.Presheaf.germ C.obj U x hx c
          ⊗ₜ[stalk (C := CommRingCat) D.obj x,((stalkFunctor CommRingCat x).map r.hom).hom]
          TopCat.Presheaf.germ M.val.presheaf U x hx m)) : g = h := by
  apply AddMonoidHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul c m =>
    obtain ⟨U, hxU, c, rfl⟩ := TopCat.Presheaf.exists_germ_eq C.obj c
    obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← TopCat.Presheaf.germ_res_apply C.obj
      (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx c,
      ← TopCat.Presheaf.germ_res_apply M.val.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m]
    exact hgh (U ⊓ V) hx _ _

/-- A fixed comparison morphism with the tensor-unit formula is invertible over a
pushout of ring sheaves. This concerns one module and does not construct the comparison
or assert naturality in the module.

Source: Stacks Project, Tag 01SB, tensor construction and elucidation in
`lemma-affine-equivalence-modules`; Tag 008A, `lemma-adjointness-tensor-restrict`.
(blueprint: lem-weil-pbc-sheaf-tensor-pushout-comparison-is-iso).

Proof: C-linearity and the unit formula give the formula on every pure tensor:
f(theta_r(c tensor m)) = theta_t(b(c) tensor m). The stalk functor from sheaves
of commutative rings is left adjoint to the skyscraper functor, so it preserves
pushouts. Give the stalks their algebra structures via the induced ring maps;
the square equation gives the two scalar towers. Restriction of module scalars
commutes with the stalk action: represent the scalar and vector on a common
intersection of neighborhoods and use the germ scalar formula. The library's
stalk change-of-rings isomorphisms identify the source and target stalk modules
with C_x tensor over D_x with M_x and B_x tensor over A_x with M_x. Mathlib's
Algebra.IsPushout.cancelBaseChange gives an equivalence between these tensors.
On pure tensor germs it is c_x tensor m_x to b_x(c_x) tensor m_x. The formula for
f and the germ formulas of the stalk comparisons identify the induced stalk map
with this equivalence. Tensor induction extends the equality to all stalk tensors;
the two stalk comparisons are bijective, so the stalk map of f is bijective.
The underlying abelian sheaf morphism is therefore an isomorphism by stalk
conservativity, and forgetting the module structure reflects isomorphisms.
All arguments allow zero rings, zero modules, and empty opens. -/
theorem sheafTensorPushoutComparison_isIso
    (r : D ⟶ C) (s : D ⟶ A) (b : C ⟶ B) (t : A ⟶ B)
    (hp : IsPushout r s b t) (M : SheafOfModules.{u} (𝓡 A))
    (f : changeOfRings.{u, u, u} r ((restrictScalars (𝓻 s)).obj M) ⟶
      (restrictScalars (𝓻 b)).obj (changeOfRings.{u, u, u} t M))
    (hf : ∀ (W : (Opens T)ᵒᵖ) (m : M.val.obj W),
      f.val.app W
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C).obj)).unit.app
          (changeOfRingsPresheaf.{u, u, u} r ((restrictScalars (𝓻 s)).obj M))).app W
          ((1 : C.obj.obj W) ⊗ₜ[D.obj.obj W,(r.hom.app W).hom] m)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
        (changeOfRingsPresheaf.{u, u, u} t M)).app W
        ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W,(t.hom.app W).hom] m)) :
    IsIso f := by
  classical
  let F := SheafOfModules.toSheaf (𝓡 C)
  suffices IsIso (F.map f) by exact isIso_of_reflects_iso f F
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (F.map f)).mpr
  intro x
  let Dx := TopCat.Presheaf.stalk (C := CommRingCat.{u}) D.obj x
  let Cx := TopCat.Presheaf.stalk (C := CommRingCat.{u}) C.obj x
  let Ax := TopCat.Presheaf.stalk (C := CommRingCat.{u}) A.obj x
  let Bx := TopCat.Presheaf.stalk (C := CommRingCat.{u}) B.obj x
  let rx := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map r.hom).hom
  let sx := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map s.hom).hom
  let bx := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map b.hom).hom
  let tx := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map t.hom).hom
  let Mx := TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x
  let : Algebra Dx Cx := rx.toAlgebra
  let : Algebra Dx Ax := sx.toAlgebra
  let : Algebra Cx Bx := bx.toAlgebra
  let : Algebra Ax Bx := tx.toAlgebra
  let : Algebra Dx Bx := (bx.comp rx).toAlgebra
  have hx : bx.comp rx = tx.comp sx := by
    have h := (stalkPushout r s b t hp x).w
    exact congrArg CommRingCat.Hom.hom h
  let : IsScalarTower Dx Cx Bx := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower Dx Ax Bx := IsScalarTower.of_algebraMap_eq' hx
  let : Algebra.IsPushout Dx Cx Ax Bx :=
    CommRingCat.isPushout_iff_isPushout.mp (stalkPushout r s b t hp x)
  let : Module Ax Mx := inferInstanceAs (Module
    (TopCat.Presheaf.stalk (C := CommRingCat.{u}) A.obj x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x))
  let : Module Dx Mx := inferInstanceAs (Module
    (TopCat.Presheaf.stalk (C := CommRingCat.{u}) D.obj x)
    (TopCat.Presheaf.stalk (C := Ab.{u}) ((restrictScalars (𝓻 s)).obj M).val.presheaf x))
  let : IsScalarTower Dx Ax Mx :=
    IsScalarTower.of_algebraMap_smul (fun d m ↦ (stalkRestrict_smul s M x d m).symm)
  let E := (Algebra.IsPushout.cancelBaseChange Dx Cx Ax Bx Mx).symm
  obtain ⟨Φr, hΦr, _⟩ := stalkChangeOfRingsIso T D C r x
  obtain ⟨Φt, hΦt, _⟩ := stalkChangeOfRingsIso T A B t x
  let hr := Φr ((restrictScalars (𝓻 s)).obj M)
  let ht := Φt M
  have he : Function.Bijective E := E.bijective
  let gr := hr.hom.hom.toAddMonoidHom
  let gt := ht.hom.hom.toAddMonoidHom
  let g := PresheafOfModules.stalkAddMap (x := x) f.val
  have hcomp : g.comp gr = gt.comp E.toLinearMap.toAddMonoidHom := by
    apply stalkTensor_addHom_ext r ((restrictScalars (𝓻 s)).obj M) x
    intro U hxU c m
    let cx : Cx := TopCat.Presheaf.germ C.obj U x hxU c
    let mx : Mx := TopCat.Presheaf.germ M.val.presheaf U x hxU m
    let z := c ⊗ₜ[D.obj.obj (Opposite.op U), (r.hom.app (Opposite.op U)).hom]
      (show ((restrictScalars (𝓻 s)).obj M).val.obj (Opposite.op U) from m)
    let w := b.hom.app (Opposite.op U) c
      ⊗ₜ[A.obj.obj (Opposite.op U), (t.hom.app (Opposite.op U)).hom]
        (show M.val.obj (Opposite.op U) from m)
    change g (gr (cx ⊗ₜ[Dx] mx)) = gt (E (cx ⊗ₜ[Dx] mx))
    have hleft : g (gr (cx ⊗ₜ[Dx] mx)) =
        TopCat.Presheaf.germ (changeOfRings t M).val.presheaf U x hxU
          ((θ t M).app (Opposite.op U) w) :=
      (congrArg g (hΦr ((restrictScalars (𝓻 s)).obj M) U hxU m c)).trans
        ((TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
          ((PresheafOfModules.toPresheaf _).map f.val)
          ((θ r((restrictScalars (𝓻 s)).obj M)).app (Opposite.op U) z)).trans
          (congrArg (TopCat.Presheaf.germ (changeOfRings t M).val.presheaf U x hxU)
            (comparison_formula r s b t M f hf (Opposite.op U) c m)))
    have hbx : bx cx = TopCat.Presheaf.germ B.obj U x hxU
        (b.hom.app (Opposite.op U) c) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU b.hom c
    have hright : gt (E (cx ⊗ₜ[Dx] mx)) =
        TopCat.Presheaf.germ (changeOfRings t M).val.presheaf U x hxU
          ((θ t M).app (Opposite.op U) w) :=
      (congrArg gt (Algebra.IsPushout.cancelBaseChange_symm_tmul Dx Cx Ax Bx Mx cx mx)).trans
        ((congrArg (fun c : Bx ↦ gt (c ⊗ₜ[Ax] mx)) hbx).trans
          (hΦt M U hxU m (b.hom.app (Opposite.op U) c)))
    exact hleft.trans hright.symm
  have hg : Function.Bijective g := by
    have hgr : Function.Bijective gr := ConcreteCategory.bijective_of_isIso hr.hom
    have hgt : Function.Bijective gt := ConcreteCategory.bijective_of_isIso ht.hom
    have hh : g ∘ gr = gt ∘ E := congrArg DFunLike.coe hcomp
    have hb : Function.Bijective (g ∘ gr) := by
      rw [hh]
      exact hgt.comp he
    exact (hgr.of_comp_iff g).mp hb
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hg

end
end SheafOfModules
