/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Sheaf frames from section bases of finite-free retracts

Source: Stacks Project, Tag 0BF2, and finite-projective module algebra.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
noncomputable section
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (T : C) (hT : IsTerminal T)

private def homAt (M : SheafOfModules.{w} R) :
    (unit R ⟶ M) ≃+ M.val.obj (op T) where
  toFun f := f.val.app (op T) (1 : R.obj.obj (op T))
  invFun x := M.unitHomEquiv.symm (M.val.sectionsMk
    (fun V ↦ M.val.map (hT.from V.unop).op x)
    (fun V W k ↦ by
      rw [← M.val.map_comp_apply]
      have hk : (hT.from V.unop).op ≫ k = (hT.from W.unop).op := by
        apply Quiver.Hom.unop_inj
        exact hT.hom_ext _ _
      rw [hk]))
  left_inv f := by
    apply M.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro V
    exact PresheafOfModules.sections_property (M.unitHomEquiv f) (hT.from V.unop).op
  right_inv x := by
    have h := M.unitHomEquiv.apply_symm_apply (M.val.sectionsMk
      (fun V ↦ M.val.map (hT.from V.unop).op x)
      (fun V W k ↦ by
      rw [← M.val.map_comp_apply]
      have hk : (hT.from V.unop).op ≫ k = (hT.from W.unop).op := by
        apply Quiver.Hom.unop_inj
        exact hT.hom_ext _ _
      rw [hk]))
    have he := congrArg (fun s ↦ s.val (op T)) h
    change _ = M.val.map (hT.from T).op x at he
    rw [show hT.from T = 𝟙 T from hT.hom_ext _ _, op_id, M.val.map_id] at he
    exact he
  map_add' f g := rfl

include hT

private lemma retract_hom_ext {M N : SheafOfModules.{w} R} {I : Type w}
    (ι : M ⟶ free I) (π : free I ⟶ M) (h : ι ≫ π = 𝟙 M)
    {f g : M ⟶ N} (he : f.val.app (op T) = g.val.app (op T)) : f = g := by
  have he' : π ≫ f = π ≫ g := by
    apply free_hom_ext
    intro i
    apply (homAt T hT N).injective
    change f.val.app (op T) _ = g.val.app (op T) _
    rw [he]
  calc f = ι ≫ (π ≫ f) := by rw [← Category.assoc, h, Category.id_comp]
       _ = ι ≫ (π ≫ g) := congrArg (ι ≫ ·) he'
       _ = g := by rw [← Category.assoc, h, Category.id_comp]

private lemma free_hom_ext_top {M : SheafOfModules.{w} R} {I : Type w}
    {f g : free I ⟶ M} (he : f.val.app (op T) = g.val.app (op T)) : f = g :=
  retract_hom_ext T hT (𝟙 _) (𝟙 _) (by simp) he

private lemma isIso_free_of_retract {M : SheafOfModules.{w} R} {I A : Type w}
    (ι : M ⟶ free A) (π : free A ⟶ M) (h : ι ≫ π = 𝟙 M)
    (g : free I ⟶ M) (hg : Function.Bijective (g.val.app (op T))) : IsIso g := by
  let ψ : free A ⟶ free I := (freeHomEquiv (free I)).symm
    (fun a ↦ (free I).unitHomEquiv
      ((homAt T hT (free I)).symm
        (Function.invFun (g.val.app (op T))
          ((ιFree a ≫ π).val.app (op T) (1 : R.obj.obj (op T))))))
  have hψ : ψ ≫ g = π := by
    apply free_hom_ext
    intro a
    apply (homAt T hT M).injective
    change g.val.app (op T) ((ιFree a ≫ ψ).val.app (op T) (1 : R.obj.obj (op T))) = _
    have hψa : ιFree a ≫ ψ = (homAt T hT (free I)).symm
        (Function.invFun (g.val.app (op T))
          ((ιFree a ≫ π).val.app (op T) (1 : R.obj.obj (op T)))) := by
      apply (free I).unitHomEquiv.injective
      exact congrFun ((freeHomEquiv (free I)).apply_symm_apply _) a
    rw [hψa]
    change g.val.app (op T) (homAt T hT (free I) ((homAt T hT (free I)).symm _)) = _
    rw [AddEquiv.apply_symm_apply]
    exact Function.invFun_eq (hg.2 _)
  let k := ι ≫ ψ
  have hk : k ≫ g = 𝟙 M := by
    dsimp only [k]
    rw [Category.assoc, hψ, h]
  have hgk : g ≫ k = 𝟙 _ := by
    apply free_hom_ext_top T hT
    ext x
    apply hg.1
    change ((g ≫ k) ≫ g).val.app (op T) x = (𝟙 _ ≫ g).val.app (op T) x
    rw [Category.assoc, hk, Category.comp_id, Category.id_comp]
  exact ⟨⟨k, hgk, hk⟩⟩

private lemma exists_iso_free_sections {M : SheafOfModules.{w} R} {I A : Type w}
    [Fintype I] [DecidableEq I]
    (ι : M ⟶ free A) (π : free A ⟶ M) (h : ι ≫ π = 𝟙 M)
    (e : M.val.obj (op T) ≃ₗ[R.obj.obj (op T)] (I → R.obj.obj (op T))) :
    ∃ q : M ≅ free I,
      ∀ x, freeSectionsLinearEquiv I (op T) (q.hom.val.app (op T) x) = e x := by
  let b := Pi.basisFun (R.obj.obj (op T)) I
  let g : free I ⟶ M := M.freeHomEquiv.symm
    (fun i ↦ M.unitHomEquiv ((homAt T hT M).symm (e.symm (b i))))
  have hgi (i : I) : (ιFree i ≫ g).val.app (op T) (1 : R.obj.obj (op T)) = e.symm (b i) := by
    have hi : ιFree i ≫ g = (homAt T hT M).symm (e.symm (b i)) := by
      apply M.unitHomEquiv.injective
      exact congrFun (M.freeHomEquiv.apply_symm_apply _) i
    change homAt T hT M (ιFree i ≫ g) = _
    rw [hi, AddEquiv.apply_symm_apply]
  let c := freeSectionsLinearEquiv (R := R) I (op T)
  have hgc : e.toLinearMap.comp ((g.val.app (op T)).hom.comp c.symm.toLinearMap) =
      LinearMap.id := by
    apply b.ext
    intro i
    change e (g.val.app (op T) (c.symm (b i))) = b i
    have hc : c.symm (b i) = (ιFree (R := R) i).val.app (op T) (1 : R.obj.obj (op T)) := by
      apply c.injective
      rw [LinearEquiv.apply_symm_apply]
      ext j
      change b i j = (ιFree i ≫ freeπ j).val.app (op T) (1 : R.obj.obj (op T))
      rw [ιFree_freeπ]
      by_cases hij : i = j
      · subst j
        rw [ite_eq_left rfl]
        simp [b, Pi.basisFun_apply]
      · rw [ite_eq_right hij]
        simp only [b, Pi.basisFun_apply, Pi.single_apply, ite_eq_right (Ne.symm hij)]
        rfl
    rw [hc]
    change e ((ιFree i ≫ g).val.app (op T) (1 : R.obj.obj (op T))) = _
    rw [hgi, LinearEquiv.apply_symm_apply]
  have hge (x : (free (R := R) I).val.obj (op T)) :
      e (g.val.app (op T) x) = c x := by
    have he := LinearMap.congr_fun hgc (c x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply] using he
  have hg : Function.Bijective (g.val.app (op T)) := by
    constructor
    · intro x y hxy
      apply c.injective
      rw [← hge x, ← hge y, hxy]
    · intro x
      refine ⟨c.symm (e x), e.injective ?_⟩
      rw [hge, LinearEquiv.apply_symm_apply]
  have := isIso_free_of_retract T hT ι π h g hg
  refine ⟨(asIso g).symm, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := hg.2 x
  change c ((inv g).val.app (op T) (g.val.app (op T) y)) = _
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← comp_val,
    IsIso.hom_inv_id]
  exact (hge y).symm

private lemma exists_iso_unit_sections {M : SheafOfModules.{w} R} {A : Type w}
    (ι : M ⟶ free A) (π : free A ⟶ M) (h : ι ≫ π = 𝟙 M)
    (e : M.val.obj (op T) ≃ₗ[R.obj.obj (op T)] R.obj.obj (op T)) :
    ∃ q : M ≅ unit R, ∀ x, q.hom.val.app (op T) x = e x := by
  let e' := e.trans (LinearEquiv.funUnique PUnit.{w + 1}
    (R.obj.obj (op T)) (R.obj.obj (op T))).symm
  obtain ⟨q, hq⟩ := exists_iso_free_sections T hT ι π h e'
  let j := freeUniqueIso (R := R) PUnit.{w + 1}
  refine ⟨q ≪≫ j, ?_⟩
  intro x
  have hj : j.hom = freeπ (R := R) (default : PUnit.{w + 1}) := by
    apply free_hom_ext
    intro i
    change Sigma.ι (fun _ : PUnit.{w + 1} ↦ unit R) i ≫
      (coproductUniqueIso _).hom = _
    rw [ι_coproductUniqueIso_hom, ιFree_freeπ]
    simp
  change j.hom.val.app (op T) (q.hom.val.app (op T) x) = _
  rw [hj]
  exact congrFun (hq x) default

end
end SheafOfModules

namespace AlgebraicGeometry.Scheme
open Modules
private lemma overUnit_scalar_top (W : Scheme.{w}) (U : W.Opens)
    (f : SheafOfModules.unit (W.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (W.ringCatSheaf.over U)) :
    Modules.Hom.app ((Modules.overEquiv U).functor.map f) ⊤ (1 : Γ(U.toScheme, ⊤)) =
      U.topIso.inv (f.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U))) := by
  change f.val.app (.op (U.overEquivalence.inverse.obj ⊤)) (1 : Γ(U.toScheme, ⊤)) = _
  have h := f.val.naturality (Over.mkIdTerminal.from
    (U.overEquivalence.inverse.obj ⊤)).op
  have he := congrArg (fun k ↦ k (1 : Γ(W, U))) h
  change f.val.app (.op (U.overEquivalence.inverse.obj ⊤))
      (W.presheaf.map _ (1 : Γ(W, U))) = W.presheaf.map _
        (f.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U))) at he
  rw [map_one] at he
  rw [Opens.topIso_inv]
  have hmap : ((Over.forget U).op.map
      (Over.mkIdTerminal.from (U.overEquivalence.inverse.obj ⊤)).op) =
      (eqToHom U.ι_image_top).op := Subsingleton.elim _ _
  rw [hmap] at he
  exact he
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
noncomputable section
open Modules
private def overFreeIso (W : Scheme.{w}) (U : W.Opens) (I : Type w) :
    (Modules.overEquiv U).functor.obj
      (SheafOfModules.free (R := W.ringCatSheaf.over U) I) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
  (SheafOfModules.mapFreeIso (Modules.overEquiv U).functor I
    (U.sheafOfModulesEquivOverUnit W.ringCatSheaf).symm).symm

private lemma overFree_projection (W : Scheme.{w}) (U : W.Opens)
    (I : Type w) [DecidableEq I] (i : I) :
    (overFreeIso W U I).hom ≫ Modules.freeπ i =
      (Modules.overEquiv U).functor.map (SheafOfModules.freeπ i) ≫
        (U.sheafOfModulesEquivOverUnit W.ringCatSheaf).hom := by
  apply (cancel_epi (overFreeIso W U I).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply Modules.free_hom_ext
  intro j
  have hi : SheafOfModules.ιFree j ≫ (overFreeIso W U I).inv =
      (U.sheafOfModulesEquivOverUnit W.ringCatSheaf).inv ≫
        (Modules.overEquiv U).functor.map (SheafOfModules.ιFree j) :=
    SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _
  rw [reassoc_of% hi, ← Functor.map_comp_assoc, SheafOfModules.ιFree_freeπ,
    Modules.ιFree_freeπ]
  split_ifs <;> simp

/-- The section bases realize the differential as a column of sheaf maps.
Source: Stacks Project, Tag 0BF2, degree-zero calculation, and the finite-projective
module argument applied to sheaves of modules.
(blueprint: lem-sc-picard-ordinary-affine-differential-frames)

Proof: Maps from the unit sheaf are sections at the terminal object. Therefore
maps out of a retract of a free sheaf are determined by their terminal section
maps. Given a section basis, send each free generator to its inverse image under
the basis. This sheaf map is bijective on terminal sections. To construct its
inverse, lift the generators of a free sheaf of which the term is a retract,
using the inverse terminal section map, and compose with the retract inclusion.
Equality on terminal sections proves both inverse identities. Apply this to the
rank-one basis and to the finite coordinate basis, then transport the resulting
isomorphisms through the open-site equivalence. The equivalence preserves the
unit, free coproducts and their projections. Evaluate hd at one to identify the
column, and transport its coefficients with U.topIso. The argument includes
m=0 and needs no affine tilde construction. -/
theorem picard_ordinary_affine_differential_frames
    (W : Scheme.{v}) (U : W.Opens) (_hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hd : ∀ a : Γ(W, U),
      e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d) :
    ∃ (q0 : (Modules.overEquiv U).functor.obj (K.X 0) ≅ Modules.unit U.toScheme)
      (q1 : (Modules.overEquiv U).functor.obj (K.X 1) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{v} (Fin m))),
      ∀ i : Fin m,
        Modules.freeSectionsEquiv (ULift.{v} (Fin m))
          (Modules.Hom.app
            (q0.inv ≫ (Modules.overEquiv U).functor.map (K.d 0 1) ≫ q1.hom)
            ⊤ (1 : Γ(U.toScheme, ⊤))) ⟨i⟩ = U.topIso.inv (d i) := by
  classical
  obtain ⟨a0, ι0, π0, h0⟩ := hK.2 0
  obtain ⟨a1, ι1, π1, h1⟩ := hK.2 1
  obtain ⟨r0, hr0⟩ := SheafOfModules.exists_iso_unit_sections
    (Over.mk (𝟙 U)) Over.mkIdTerminal ι0 π0 h0 e0
  let e1' : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)]
      (ULift.{v} (Fin m) → Γ(W, U)) :=
    e1.trans
      { toFun := fun a i ↦ a i.down
        invFun := fun a i ↦ a ⟨i⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  obtain ⟨r1, hr1⟩ := SheafOfModules.exists_iso_free_sections
    (Over.mk (𝟙 U)) Over.mkIdTerminal ι1 π1 h1 e1'
  let F := (Modules.overEquiv U).functor
  let q0 := F.mapIso r0 ≪≫ U.sheafOfModulesEquivOverUnit W.ringCatSheaf
  let q1 := F.mapIso r1 ≪≫ overFreeIso W U (ULift.{v} (Fin m))
  let φ := r0.inv ≫ K.d 0 1 ≫ r1.hom
  have hφ (i : Fin m) :
      (SheafOfModules.freeπ (ULift.up i) :
        SheafOfModules.free (R := W.ringCatSheaf.over U) (ULift.{v} (Fin m)) ⟶ _).val.app
        (.op (Over.mk (𝟙 U)))
        (φ.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U))) = d i := by
    have hinv : r0.inv.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U)) = e0.symm 1 := by
      apply e0.injective
      calc
        e0 (r0.inv.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U))) =
            r0.hom.val.app (.op (Over.mk (𝟙 U)))
              (r0.inv.val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U))) := (hr0 _).symm
        _ = (1 : Γ(W, U)) := by
          change (r0.inv ≫ r0.hom).val.app (.op (Over.mk (𝟙 U))) (1 : Γ(W, U)) = _
          rw [r0.inv_hom_id]
          rfl
        _ = e0 (e0.symm 1) := (e0.apply_symm_apply _).symm
    change SheafOfModules.freeSectionsLinearEquiv (ULift.{v} (Fin m))
      (.op (Over.mk (𝟙 U)))
      (r1.hom.val.app _ ((K.d 0 1).val.app _ (r0.inv.val.app _ (1 : Γ(W, U))))) ⟨i⟩ = _
    rw [hr1, hinv]
    change e1 ((K.d 0 1).val.app _ (e0.symm 1)) i = _
    rw [hd, one_smul]
  refine ⟨q0, q1, ?_⟩
  intro i
  change Modules.Hom.app (Modules.freeπ (ULift.up i)) ⊤
    (Modules.Hom.app (q0.inv ≫ F.map (K.d 0 1) ≫ q1.hom) ⊤
      (1 : Γ(U.toScheme, ⊤))) = _
  rw [← ConcreteCategory.comp_apply, ← Modules.Hom.comp_app]
  have hc : q0.inv ≫ F.map (K.d 0 1) ≫ q1.hom ≫ Modules.freeπ (ULift.up i) =
      (U.sheafOfModulesEquivOverUnit W.ringCatSheaf).inv ≫
        F.map (φ ≫ SheafOfModules.freeπ (ULift.up i)) ≫
          (U.sheafOfModulesEquivOverUnit W.ringCatSheaf).hom := by
    dsimp only [q0, q1, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc, Category.assoc, overFree_projection]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  simp only [Category.assoc]
  rw [hc]
  change Modules.Hom.app (F.map (φ ≫ SheafOfModules.freeπ (ULift.up i))) ⊤
    (1 : Γ(U.toScheme, ⊤)) = _
  rw [overUnit_scalar_top]
  congr 1
  exact hφ i

end
end AlgebraicGeometry.Scheme
