/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Alternating wedges of germs before sheafification
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

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

set_option backward.isDefEq.respectTransparency false in
private theorem exteriorWedge_res {X : Scheme.{v}} (M : X.Modules) (n : ℕ) (x : X)
    {U V : X.Opens} (f : V ⟶ U) (hx : x ∈ V) (a : Fin n → M.val.obj (op U)) :
    TopCat.Presheaf.germ (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf
        V x hx (exteriorPower.ιMulti (X.presheaf.obj (op V)) n
          (fun i ↦ M.val.map f.op (a i))) =
      TopCat.Presheaf.germ (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf
        U x (f.le hx) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a) := by
  let P := PresheafOfModules.exteriorPower (R := X.presheaf) M.val n
  have hr := PresheafOfModules.exteriorPower_map_ιMulti (R := X.presheaf) M.val n f.op a
  exact (congrArg (TopCat.Presheaf.germ P.presheaf V x hx) hr.symm).trans
    (TopCat.Presheaf.germ_res_apply P.presheaf f x hx _)

set_option backward.isDefEq.respectTransparency false in
private theorem commonEquality {X : Scheme.{v}} (M : X.Modules) (n : ℕ) (x : X)
    {U V : X.Opens} (hxU : x ∈ U) (hxV : x ∈ V)
    (a : Fin n → M.val.obj (op U)) (b : Fin n → M.val.obj (op V))
    (h : ∀ i, M.presheaf.germ U x hxU (a i) = M.presheaf.germ V x hxV (b i)) :
    ∃ (W : X.Opens) (_hxW : x ∈ W) (f : W ⟶ U) (g : W ⟶ V),
      ∀ i, M.val.map f.op (a i) = M.val.map g.op (b i) := by
  classical
  have H (S : Finset (Fin n)) :
      ∃ (W : X.Opens) (_hxW : x ∈ W) (f : W ⟶ U) (g : W ⟶ V),
        ∀ i ∈ S, M.val.map f.op (a i) = M.val.map g.op (b i) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨U ⊓ V, ⟨hxU, hxV⟩, homOfLE inf_le_left,
        homOfLE inf_le_right, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨W, hxW, f, g, hS⟩ := ih
      obtain ⟨Z, hxZ, f', g', he⟩ := M.presheaf.germ_eq x hxU hxV (a i) (b i) (h i)
      let l : W ⊓ Z ⟶ W := homOfLE inf_le_left
      let r : W ⊓ Z ⟶ Z := homOfLE inf_le_right
      refine ⟨W ⊓ Z, ⟨hxW, hxZ⟩, l ≫ f, l ≫ g, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hj | hj
      · subst j
        change M.val.map f'.op (a i) = M.val.map g'.op (b i) at he
        have he' := congrArg (M.val.map r.op) he
        have e₁ : l ≫ f = r ≫ f' := Subsingleton.elim _ _
        have e₂ : l ≫ g = r ≫ g' := Subsingleton.elim _ _
        rw [e₁, e₂]
        change M.val.map (f'.op ≫ r.op) (a i) = M.val.map (g'.op ≫ r.op) (b i)
        rw [M.val.map_comp_apply, M.val.map_comp_apply]
        exact he'
      · change M.val.map (f.op ≫ l.op) (a j) = M.val.map (g.op ≫ l.op) (b j)
        rw [M.val.map_comp_apply, M.val.map_comp_apply, hS j hj]
  obtain ⟨W, hxW, f, g, hW⟩ := H Finset.univ
  exact ⟨W, hxW, f, g, fun i ↦ hW i (Finset.mem_univ i)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Sectionwise wedge germs descend to an alternating map on module stalks. -/
theorem exteriorPresheaf_stalk_wedge {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ b : (M.presheaf.stalk x) [⋀^Fin n]→ₗ[X.presheaf.stalk x]
        (TopCat.Presheaf.stalk (C := Ab.{v})
          (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        b (fun i ↦ M.presheaf.germ U x hx (a i)) =
          TopCat.Presheaf.germ
            (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n).presheaf U x hx
            (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a) := by
  classical
  let P := (PresheafOfModules.exteriorPower (R := X.presheaf) M.val n)
  let T := TopCat.Presheaf.stalk (C := Ab.{v}) P.presheaf x
  let A := X.presheaf.stalk x
  have uniq (U V : X.Opens) (hxU : x ∈ U) (hxV : x ∈ V)
      (a : Fin n → M.val.obj (op U)) (b : Fin n → M.val.obj (op V))
      (h : ∀ i, M.presheaf.germ U x hxU (a i) = M.presheaf.germ V x hxV (b i)) :
      TopCat.Presheaf.germ P.presheaf U x hxU (exteriorPower.ιMulti _ n a) =
        TopCat.Presheaf.germ P.presheaf V x hxV (exteriorPower.ιMulti _ n b) := by
    obtain ⟨W, hxW, f, g, he⟩ := commonEquality M n x hxU hxV a b h
    have ha := exteriorWedge_res M n x f hxW a
    have hb := exteriorWedge_res M n x g hxW b
    exact ha.symm.trans ((congrArg
      (fun t ↦ TopCat.Presheaf.germ P.presheaf W x hxW (exteriorPower.ιMulti _ n t))
      (funext he)).trans hb)
  have ex (a : Fin n → M.presheaf.stalk x) : ∃ z : T, ∃ (U : X.Opens) (hx : x ∈ U)
      (s : Fin n → M.val.obj (op U)),
      (∀ i, M.presheaf.germ U x hx (s i) = a i) ∧
        TopCat.Presheaf.germ P.presheaf U x hx (exteriorPower.ιMulti _ n s) = z := by
    obtain ⟨U, hx, s, hs⟩ := commonGerms M x n a
    exact ⟨_, U, hx, s, hs, rfl⟩
  let b (a : Fin n → M.presheaf.stalk x) : T := (ex a).choose
  have hb (U : X.Opens) (hx : x ∈ U) (s : Fin n → M.val.obj (op U)) :
      b (fun i ↦ M.presheaf.germ U x hx (s i)) =
        TopCat.Presheaf.germ P.presheaf U x hx (exteriorPower.ιMulti _ n s) := by
    obtain ⟨V, hxV, t, ht, hz⟩ := (ex (fun i ↦ M.presheaf.germ U x hx (s i))).choose_spec
    exact hz.symm.trans (uniq V U hxV hx t s ht)
  have rep (a : Fin n → M.presheaf.stalk x) (s t : M.presheaf.stalk x) :
      ∃ (U : X.Opens) (hx : x ∈ U) (v : Fin n → M.val.obj (op U))
        (s' t' : M.val.obj (op U)),
        (∀ i, M.presheaf.germ U x hx (v i) = a i) ∧
          M.presheaf.germ U x hx s' = s ∧ M.presheaf.germ U x hx t' = t := by
    obtain ⟨U, hx, v, hv⟩ := commonGerms M x (n + 2) (Fin.append a ![s, t])
    refine ⟨U, hx, (fun i ↦ v (i.castAdd 2)), v (Fin.natAdd n 0),
      v (Fin.natAdd n 1), ?_, ?_, ?_⟩
    · intro i
      simpa only [Fin.append_left] using hv (i.castAdd 2)
    · simpa using hv (Fin.natAdd n 0)
    · simpa using hv (Fin.natAdd n 1)
  have add (a : Fin n → M.presheaf.stalk x) (i : Fin n) (s t : M.presheaf.stalk x) :
      b (Function.update a i (s + t)) = b (Function.update a i s) +
        b (Function.update a i t) := by
    obtain ⟨U, hx, v, s', t', hv, hs, ht⟩ := rep a s t
    have ha : a = fun j ↦ M.presheaf.germ U x hx (v j) := funext fun j ↦ (hv j).symm
    have hc (z : M.val.obj (op U)) :
        Function.update (fun j ↦ M.presheaf.germ U x hx (v j)) i
          (M.presheaf.germ U x hx z) =
          (fun j ↦ M.presheaf.germ U x hx (Function.update v i z j)) := by
      funext j
      by_cases h : j = i <;> simp [h]
    rw [ha, ← hs, ← ht, ← map_add, hc, hc, hc, hb, hb, hb]
    rw [(exteriorPower.ιMulti _ n).map_update_add, map_add]
  have smul (a : Fin n → M.presheaf.stalk x) (i : Fin n) (r : A) (s : M.presheaf.stalk x) :
      b (Function.update a i (r • s)) = r • b (Function.update a i s) := by
    obtain ⟨U, hxU, v, s', t', hv, hs, ht⟩ := rep a s s
    obtain ⟨V, hVU, hxV, r', hr⟩ := X.presheaf.exists_le_germ_eq r hxU
    let f : V ⟶ U := homOfLE hVU
    let w : Fin n → M.val.obj (op V) := fun j ↦ M.val.map f.op (v j)
    let t : M.val.obj (op V) := M.val.map f.op s'
    have hw : ∀ j, M.presheaf.germ V x hxV (w j) = a j := by
      intro j
      exact (M.presheaf.germ_res_apply f x hxV (v j)).trans (hv j)
    have ht : M.presheaf.germ V x hxV t = s :=
      (M.presheaf.germ_res_apply f x hxV s').trans hs
    have ha : a = fun j ↦ M.presheaf.germ V x hxV (w j) := funext fun j ↦ (hw j).symm
    have hc (z : M.val.obj (op V)) :
        Function.update (fun j ↦ M.presheaf.germ V x hxV (w j)) i
          (M.presheaf.germ V x hxV z) =
          (fun j ↦ M.presheaf.germ V x hxV (Function.update w i z j)) := by
      funext j
      by_cases h : j = i <;> simp [h]
    rw [ha, ← ht, ← hr, ← germ_smul, hc, hc, hb, hb]
    rw [(exteriorPower.ιMulti _ n).map_update_smul]
    exact PresheafOfModules.germ_smul (R := X.presheaf) P x V hxV r' _
  have alt (a : Fin n → M.presheaf.stalk x) (i j : Fin n)
      (h : a i = a j) (hne : i ≠ j) : b a = 0 := by
    obtain ⟨U, hxU, v, hv⟩ := commonGerms M x n a
    have he : M.presheaf.germ U x hxU (v i) = M.presheaf.germ U x hxU (v j) :=
      (hv i).trans (h.trans (hv j).symm)
    obtain ⟨V, hxV, f, g, he⟩ := M.presheaf.germ_eq x hxU hxU (v i) (v j) he
    have hfg : g = f := Subsingleton.elim _ _
    change M.val.map f.op (v i) = M.val.map g.op (v j) at he
    rw [hfg] at he
    let w : Fin n → M.val.obj (op V) := fun k ↦ M.val.map f.op (v k)
    have hw : a = fun k ↦ M.presheaf.germ V x hxV (w k) := by
      funext k
      exact ((M.presheaf.germ_res_apply f x hxV (v k)).trans (hv k)).symm
    rw [hw, hb]
    rw [(exteriorPower.ιMulti _ n).map_eq_zero_of_eq w he hne]
    exact map_zero _
  let B : (M.presheaf.stalk x) [⋀^Fin n]→ₗ[X.presheaf.stalk x] T :=
    { toFun := b
      map_update_add' := by
        intro d a i s t
        have hd : d = instDecidableEqFin n := Subsingleton.elim _ _
        subst d
        exact add a i s t
      map_update_smul' := by
        intro d a i r s
        have hd : d = instDecidableEqFin n := Subsingleton.elim _ _
        subst d
        exact smul a i r s
      map_eq_zero_of_eq' := alt }
  exact ⟨B, hb⟩

end AlgebraicGeometry.Scheme.Modules
