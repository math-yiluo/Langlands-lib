/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPresheafStalkWedge
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Exterior powers commute with module stalks

## References

* Stacks Project, Lemma 007Z
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private noncomputable def exteriorGermMap {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⋀[X.presheaf.obj (op U)]^n (M.val.obj (op U)) →ₗ[X.presheaf.obj (op U)]
      (ModuleCat.restrictScalars (X.presheaf.germ U x hx).hom).obj
        (ModuleCat.of (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x))) := by
  let A : (M.val.obj (op U)) [⋀^Fin n]→ₗ[X.presheaf.obj (op U)]
      (ModuleCat.restrictScalars (X.presheaf.germ U x hx).hom).obj
        (ModuleCat.of (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x))) :=
    { toFun := fun a ↦ exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ M.presheaf.germ U x hx (a i))
      map_update_add' := by
        intro _ a i s t
        have hc (z : M.val.obj (op U)) :
            (fun j ↦ M.presheaf.germ U x hx (Function.update a i z j)) =
              Function.update (fun j ↦ M.presheaf.germ U x hx (a j)) i
                (M.presheaf.germ U x hx z) := by
          funext j
          by_cases h : j = i <;> simp [h]
        rw [hc, hc, hc, map_add]
        exact (exteriorPower.ιMulti (X.presheaf.stalk x) n).map_update_add _ _ _ _
      map_update_smul' := by
        intro _ a i r t
        have hc (z : M.val.obj (op U)) :
            (fun j ↦ M.presheaf.germ U x hx (Function.update a i z j)) =
              Function.update (fun j ↦ M.presheaf.germ U x hx (a j)) i
                (M.presheaf.germ U x hx z) := by
          funext j
          by_cases h : j = i <;> simp [h]
        rw [hc, hc, germ_smul]
        exact (exteriorPower.ιMulti (X.presheaf.stalk x) n).map_update_smul _ _ _ _
      map_eq_zero_of_eq' := by
        intro a i j hij hne
        exact (exteriorPower.ιMulti (X.presheaf.stalk x) n).map_eq_zero_of_eq _
          (congrArg (fun t ↦ M.presheaf.germ U x hx t) hij) hne }
  exact exteriorPower.alternatingMapLinearEquiv A

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorGermMap_wedge {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)) :
    exteriorGermMap M n x U hx (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i ↦ M.presheaf.germ U x hx (a i)) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ a

-- The section-ring scalar action must be identified across exterior restrictions.
set_option backward.isDefEq.respectTransparency false in
private theorem exteriorGermMap_res {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (x : X) {U V : X.Opens} (f : V ⟶ U) (hx : x ∈ V)
    (z : ⋀[X.presheaf.obj (op U)]^n (M.val.obj (op U))) :
    exteriorGermMap M n x V hx
        (((PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).map f.op) z) =
      exteriorGermMap M n x U (f.le hx) z := by
  let L := exteriorGermMap M n x U (f.le hx)
  let K := exteriorGermMap M n x V hx
  let r := ((PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).map f.op)
  change K (r z) = L z
  have hz : z ∈ Submodule.span (X.presheaf.obj (op U))
      (Set.range (exteriorPower.ιMulti (X.presheaf.obj (op U)) n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    change exteriorGermMap M n x V hx
      (((PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).map f.op).hom
        (exteriorPower.ιMulti _ n a)) = _
    erw [(PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) M.val n f.op) a]
    erw [exteriorGermMap_wedge, exteriorGermMap_wedge]
    congr 1
    funext k
    exact M.presheaf.germ_res_apply f x hx (a k)
  | zero => simp only [map_zero]
  | add z w hz hw ihz ihw => simpa only [map_add] using congrArg₂ (· + ·) ihz ihw
  | smul a z hz ih =>
    rw [r.hom.map_smul]
    change K (X.presheaf.map f.op a •
      (show ⋀[X.presheaf.obj (op V)]^n (M.val.obj (op V)) from r z)) = L (a • z)
    rw [K.map_smul, L.map_smul]
    change X.presheaf.germ V x hx (X.presheaf.map f.op a) • K (r z) =
      X.presheaf.germ U x (f.le hx) a • L z
    rw [ih, X.presheaf.germ_res_apply f x hx a]

set_option backward.isDefEq.respectTransparency false in
private theorem commonGerms {X : Scheme.{v}} (M : X.Modules) (x : X)
    (n : ℕ) (a : Fin n → M.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)),
      ∀ i, M.presheaf.germ U x hx (s i) = a i := by
  classical
  induction n with
  | zero => exact ⟨⊤, trivial, Fin.elim0, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨U, hxU, s, hs⟩ := ih (fun i ↦ a i.castSucc)
    obtain ⟨V, hVU, hxV, t, ht⟩ := M.presheaf.exists_le_germ_eq (a (Fin.last n)) hxU
    refine ⟨V, hxV, Fin.snoc (fun i ↦ M.val.map (homOfLE hVU).op (s i)) t, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using ht
    · simp only [Fin.snoc_castSucc]
      exact (M.presheaf.germ_res_apply (homOfLE hVU) x hxV (s j)).trans (hs j)

-- Exterior powers over section rings and stalk rings require scalar-action transports.
set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise exterior power has the expected stalk comparison.
-/
private theorem exteriorPresheaf_stalk_comparison {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : TopCat.Presheaf.stalk (C := Ab.{v})
        (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf x
          ≃ₗ[X.presheaf.stalk x]
        ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e (TopCat.Presheaf.germ
            (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf U x hx
          (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)) =
          exteriorPower.ιMulti (X.presheaf.stalk x) n
            (fun i ↦ M.presheaf.germ U x hx (a i)) := by
  classical
  let P := (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n)
  let T := TopCat.Presheaf.stalk (C := Ab.{v}) P.presheaf x
  let W := ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x)
  obtain ⟨b, hb⟩ := exteriorPresheaf_stalk_wedge M n x
  let q : W →ₗ[X.presheaf.stalk x] T := exteriorPower.alternatingMapLinearEquiv b
  let c : CategoryTheory.Limits.Cocone
      ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P.presheaf) :=
    { pt := AddCommGrpCat.of W
      ι :=
        { app := fun i ↦ AddCommGrpCat.ofHom
            (exteriorGermMap M n x i.unop.1 i.unop.2).toAddMonoidHom
          naturality := by
            intro i j f
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro z
            exact exteriorGermMap_res M n x
              ((TopologicalSpace.OpenNhds.inclusion x).map f.unop) j.unop.2 z } }
  let p : T →+ W := (CategoryTheory.Limits.colimit.desc _ c).hom
  have hp (U : X.Opens) (hx : x ∈ U) (z : P.obj (op U)) :
      p (TopCat.Presheaf.germ P.presheaf U x hx z) = exteriorGermMap M n x U hx z := by
    change (CategoryTheory.Limits.colimit.ι _ (op ⟨U, hx⟩) ≫
      CategoryTheory.Limits.colimit.desc _ c) z = _
    rw [CategoryTheory.Limits.colimit.ι_desc]
    rfl
  have p_smul (r : X.presheaf.stalk x) (z : T) : p (r • z) = r • p z := by
    obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hxV, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf z
    have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
      ← TopCat.Presheaf.germ_res_apply P.presheaf
        (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx z,
      ← PresheafOfModules.germ_smul, hp, hp]
    exact (exteriorGermMap M n x (U ⊓ V) hx).map_smul _ _
  have hqp : ∀ z : T, q (p z) = z := by
    intro z
    obtain ⟨U, hx, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf z
    rw [hp]
    change q (exteriorGermMap M n x U hx
      (z : ⋀[X.presheaf.obj (op U)]^n (M.val.obj (op U)))) =
      TopCat.Presheaf.germ P.presheaf U x hx z
    have hz : z ∈ Submodule.span (X.presheaf.obj (op U))
        (Set.range (exteriorPower.ιMulti (X.presheaf.obj (op U)) n)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      rw [exteriorGermMap_wedge]
      exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b _).trans (hb U hx a)
    | zero => simp only [map_zero]
    | add z w hz hw ihz ihw =>
      simpa only [map_add] using congrArg₂ (· + ·) ihz ihw
    | smul r z hz ih =>
      rw [(exteriorGermMap M n x U hx).map_smul]
      change q (X.presheaf.germ U x hx r • exteriorGermMap M n x U hx z) = _
      rw [q.map_smul, ih]
      exact (PresheafOfModules.germ_smul (R := X.presheaf) P x U hx r z).symm
  have hpq : ∀ z : W, p (q z) = z := by
    intro z
    have hz : z ∈ Submodule.span (X.presheaf.stalk x)
        (Set.range (exteriorPower.ιMulti (X.presheaf.stalk x) n)) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      obtain ⟨U, hx, s, hs⟩ := commonGerms M x n a
      have ha : a = fun i ↦ M.presheaf.germ U x hx (s i) := funext fun i ↦ (hs i).symm
      rw [ha]
      change p (exteriorPower.alternatingMapLinearEquiv b _) = _
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hb, hp,
        exteriorGermMap_wedge]
    | zero => simp only [map_zero]
    | add z w hz hw ihz ihw =>
      simpa only [map_add] using congrArg₂ (· + ·) ihz ihw
    | smul r z hz ih =>
      rw [q.map_smul, p_smul, ih]
  let e : W ≃+ T :=
    { toFun := q
      invFun := p
      left_inv := hpq
      right_inv := hqp
      map_add' := q.map_add }
  let E : W ≃ₗ[X.presheaf.stalk x] T :=
    { __ := e
      map_smul' := q.map_smul }
  refine ⟨E.symm, ?_⟩
  intro U hx a
  change p (TopCat.Presheaf.germ P.presheaf U x hx _) = _
  rw [hp, exteriorGermMap_wedge]


/-- The sheafification unit identifies the stalk of a sectionwise exterior power with
its presheaf stalk, compatibly with the displayed wedge germs.
-/
private theorem exteriorSheaf_stalk_sheafification {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : TopCat.Presheaf.stalk (C := Ab.{v}) (exteriorPower M n).presheaf x
          ≃ₗ[X.presheaf.stalk x]
        TopCat.Presheaf.stalk (C := Ab.{v})
          (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf x,
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e ((exteriorPower M n).presheaf.germ U x hx
          (wedge (M := M) (r := n) (U := U) a)) =
          TopCat.Presheaf.germ
            (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf U x hx
            (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a) := by
  let P := (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n)
  let θ := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  let L : TopCat.Presheaf.stalk (C := Ab.{v}) P.presheaf x →ₗ[X.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := Ab.{v}) (exteriorPower M n).presheaf x :=
    { toFun := PresheafOfModules.stalkAddMap θ
      map_add' := (PresheafOfModules.stalkAddMap θ).map_add
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply
            (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx r,
          ← TopCat.Presheaf.germ_res_apply P.presheaf
            (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx m,
          ← PresheafOfModules.germ_smul]
        dsimp only [PresheafOfModules.stalkAddMap]
        erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
          TopCat.Presheaf.stalkFunctor_map_germ_apply]
        change TopCat.Presheaf.germ (exteriorPower M n).presheaf _ x hx
          ((θ.app _).hom (_ • _)) = _
        rw [(θ.app _).hom.map_smul]
        exact PresheafOfModules.germ_smul (R := X.presheaf)
          (exteriorPower M n).val x _ hx _ _ }
  have hL : Function.Bijective L := by
    let t := (TopCat.Presheaf.stalkFunctor Ab.{v} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
    let : IsIso t := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      x Ab.{v} P.presheaf
    change Function.Bijective t
    exact ConcreteCategory.bijective_of_isIso t
  let E := LinearEquiv.ofBijective L hL
  refine ⟨E.symm, ?_⟩
  intro U hx a
  apply E.injective
  rw [E.apply_symm_apply]
  change _ = PresheafOfModules.stalkAddMap θ
    (TopCat.Presheaf.germ P.presheaf U x hx
      (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a))
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map θ) _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The exterior stalk comparison, characterized on wedges of germs. -/
theorem exteriorSheaf_stalk_comparison {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : (exteriorPower M n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e ((exteriorPower M n).presheaf.germ U x hx (wedge (M := M) (r := n) (U := U) a)) =
          exteriorPower.ιMulti (X.presheaf.stalk x) n
            (fun i ↦ M.presheaf.germ U x hx (a i)) := by
  obtain ⟨e₁, h₁⟩ := exteriorSheaf_stalk_sheafification M n x
  obtain ⟨e₂, h₂⟩ := exteriorPresheaf_stalk_comparison M n x
  refine ⟨e₁.trans e₂, ?_⟩
  intro U hx a
  rw [LinearEquiv.trans_apply, h₁, h₂]

end AlgebraicGeometry.Scheme.Modules
