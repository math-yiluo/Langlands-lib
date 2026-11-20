import Langlands.Global.Arithmetic.HarrisMackeyLocalProjection
import Langlands.Global.Arithmetic.HarrisMackeyRestriction

/-! # General position for a Mackey child of a chosen tower step -/

noncomputable section

universe uF

namespace Langlands.Global.GeneralPosition

open LocalFactor.CommonClosure Weil.Local FiniteRepresentation

theorem mem_conjugate_iff {G : Type*} [Group G] {H : Subgroup G} {a w : G} :
    w ∈ conjugate H a ↔ a⁻¹ * w * a ∈ H := by
  change (MulAut.conj a⁻¹) w ∈ H ↔ _
  simp only [MulAut.conj_apply, inv_inv]

private theorem conjugateRestriction_coe {G : Type*} [Group G] (H K : Subgroup G)
    (a : G) (w : (conjugate H a).subgroupOf K) :
    (conjugateRestriction H K a w : G) = a⁻¹ * (w : K) * a := by
  change (MulAut.conj a⁻¹) ((w : K) : G) = _
  simp only [MulAut.conj_apply, inv_inv]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E T : Extension F)

local notation "TP" => T.asPadicField (p := p)
local notation "j" => intermediateWeilMap F T
local notation "WT" => weilSubgroup F T
local notation "WE" => weilSubgroup F E

variable (C : Extension (T.asPadicField (p := p))) (a : localWeilGroup F)
  (χ : weilSubgroup F E →ₜ* ℂˣ)
  (η : weilSubgroup (T.asPadicField (p := p)) C →ₜ* ℂˣ)
  (hC : ∀ w, w ∈ weilSubgroup (T.asPadicField (p := p)) C ↔
    intermediateWeilMap F T w ∈ conjugate (weilSubgroup F E) a)
  (hη : ∀ w : weilSubgroup (T.asPadicField (p := p)) C,
    η w = χ ⟨a⁻¹ * intermediateWeilMap F T w * a, mem_conjugate_iff.mp ((hC w).mp w.2)⟩)

include hC hη

local instance : (weilSubgroup (T.asPadicField (p := p)) C).FiniteIndex :=
  weilSubgroup_finiteIndex _ C

private theorem projected_constituent_irreducible (X : Extension F)
    (hTX : T.field ≤ X.field) (b : localWeilGroup TP)
    (hirr : (mackeyConstituent WE (weilSubgroup F X)
      (characterLine.{uF, 0} χ.toMonoidHom) (j b * a)).IsIrreducible) :
    (mackeyConstituent (weilSubgroup TP C)
      (weilSubgroup TP (intersect TP (rebase F T X hTX) (galoisClosure TP C)))
      (characterLine.{uF, 0} η.toMonoidHom) b).IsIrreducible := by
  let Y := rebase F T X hTX
  let M := galoisClosure TP C
  let U := weilSubgroup F X
  let V := weilSubgroup TP Y
  let N := weilSubgroup TP M
  let : N.Normal := galoisClosure_normal TP C
  let P := weilSubgroup TP (intersect TP Y M)
  let H := (conjugate (weilSubgroup TP C) b).subgroupOf P
  let S := (conjugate WE (j b * a)).subgroupOf U
  let : H.FiniteIndex := inferInstanceAs
    (((conjugate (weilSubgroup TP C) b).subgroupOf P).FiniteIndex)
  let : S.FiniteIndex := inferInstanceAs
    (((conjugate WE (j b * a)).subgroupOf U).FiniteIndex)
  let e := intermediateWeilEquiv F T
  let uT : U →* WT := Subgroup.inclusion (weilSubgroup_antitone F T X hTX)
  let i : U →* localWeilGroup TP := e.symm.toMulEquiv.toMonoidHom.comp uT
  have hi (u : U) : j (i u) = u :=
    intermediateWeilMap_equiv_symm F T (uT u)
  have hm (v : localWeilGroup TP) : v ∈ V ↔ j v ∈ U :=
    rebase_weil_mem F T X hTX v
  have hiV (u : U) : i u ∈ V := (hm _).mpr (hi u ▸ u.2)
  have hiP (u : U) : i u ∈ P :=
    weilSubgroup_antitone TP (intersect TP Y M) Y inf_le_left (hiV u)
  let ι : U →* P := i.codRestrict P hiP
  have hc (v : localWeilGroup TP) :
      v ∈ conjugate (weilSubgroup TP C) b ↔ j v ∈ conjugate WE (j b * a) := by
    rw [mem_conjugate_iff, hC, mem_conjugate_iff, mem_conjugate_iff]
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc]
  have hι (u : U) : ι u ∈ H ↔ u ∈ S := by
    change i u ∈ conjugate (weilSubgroup TP C) b ↔
      (u : localWeilGroup F) ∈ conjugate WE (j b * a)
    rw [hc, hi]
  let κ : S →* H := (ι.comp S.subtype).codRestrict H fun s => (hι s).mpr s.2
  have hNV : P = N ⊔ V := by
    let : CharZero (TP).Carrier := Algebra.charZero_of_charZero (Padic p) (TP).Carrier
    let : IsGalois (TP).Carrier M.field := by
      change IsGalois (TP).Carrier
        (IntermediateField.normalClosure (TP).Carrier C.field (AlgebraicClosure (TP).Carrier))
      infer_instance
    exact (weilSubgroup_intersect TP Y M).trans (sup_comm _ _)
  have hcover (z : P) : ∃ (h : H) (u : U), z = h * ι u := by
    have hz : (z : localWeilGroup TP) ∈ N ⊔ V := by
      rw [← hNV]
      exact z.2
    obtain ⟨n, hn, v, hv, hnv⟩ := (Subgroup.mem_sup_of_normal_left
      (s := N) (t := V)).mp hz
    have hnP : n ∈ P := hNV.symm ▸ (show N ≤ N ⊔ V from le_sup_left) hn
    have hnH : n ∈ conjugate (weilSubgroup TP C) b := by
      apply mem_conjugate_iff.mpr
      apply galoisClosure_weilSubgroup_le TP C
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem n hn b⁻¹
    let u : U := ⟨j v, (hm v).mp hv⟩
    have hv' : i u = v :=
      (intermediateWeilMap_injective F T) (hi u)
    refine ⟨⟨⟨n, hnP⟩, hnH⟩, u, Subtype.ext ?_⟩
    change (z : localWeilGroup TP) = n * i u
    rw [hv']
    exact hnv.symm
  let A := restrict (conjugateRestriction (weilSubgroup TP C) P b)
    (characterLine.{uF, 0} η.toMonoidHom)
  let B := restrict (conjugateRestriction WE U (j b * a))
    (characterLine.{uF, 0} χ.toMonoidHom)
  let eqv : FiniteRepresentation.Equiv (restrict κ A) B :=
    { toLinearEquiv := LinearEquiv.refl ℂ (ULift ℂ)
      isIntertwining' := fun s => LinearMap.ext fun x => by
        change (η (conjugateRestriction (weilSubgroup TP C) P b (κ s)) : ℂ) • x =
          (χ (conjugateRestriction WE U (j b * a) s) : ℂ) • x
        rw [hη]
        congr 2
        apply congrArg (fun w : WE => χ w)
        apply Subtype.ext
        change a⁻¹ * j (conjugateRestriction (weilSubgroup TP C) P b (κ s)) * a =
          (conjugateRestriction WE U (j b * a) s : localWeilGroup F)
        rw [conjugateRestriction_coe, conjugateRestriction_coe]
        change a⁻¹ * j (b⁻¹ * i (s : U) * b) * a =
          (j b * a)⁻¹ * (s : U) * (j b * a)
        simp only [map_mul, map_inv, hi, mul_inv_rev, mul_assoc] }
  exact induce_irreducible_of_one_coset H ι S κ (fun _ => rfl)
    (fun u => (hι u).mp) hcover A
    ((CentralEigenspaceSplitting.isIrreducible_iff_of_equiv (induceEquiv S eqv)).mpr hirr)

/-- A Mackey character of the prescribed tower field has a general-position
tower obtained by intersecting all earlier stages with its own normal closure. -/
theorem isInGeneralPosition_of_mackey_tower {n : ℕ} (tower : Fin (n + 1) → Extension F)
    (hT : ∀ i, T.field ≤ (tower i).field)
    (hb : tower (Fin.last n) = T)
    (hs : ∀ i : Fin n, IsCyclicPrimeStep F (tower i.succ) (tower i.castSucc))
    (hm : (galoisClosure TP C).field ≤ (rebase F T (tower 0) (hT 0)).field)
    (hirr : ∀ (i : Fin (n + 1)) (g : localWeilGroup F),
      (mackeyConstituent WE (weilSubgroup F (tower i))
        (characterLine.{uF, 0} χ.toMonoidHom) g).IsIrreducible) :
    IsInGeneralPosition TP C η := by
  let M := galoisClosure TP C
  let R (i : Fin (n + 1)) := rebase F T (tower i) (hT i)
  let I (i : Fin (n + 1)) := intersect TP (R i) M
  let : CharZero (TP).Carrier := Algebra.charZero_of_charZero (Padic p) (TP).Carrier
  let : IsGalois (TP).Carrier M.field := by
    change IsGalois (TP).Carrier
      (IntermediateField.normalClosure (TP).Carrier C.field (AlgebraicClosure (TP).Carrier))
    infer_instance
  have ht : (I 0).field = M.field := inf_eq_right.mpr hm
  have hb' : (I (Fin.last n)).field = ⊥ := by
    have hR : (R (Fin.last n)).field = ⊥ := by
      unfold R
      generalize hT (Fin.last n) = h
      revert h
      rw [hb]
      exact fun _ => rebase_self F T
    change (R (Fin.last n)).field ⊓ M.field = ⊥
    rw [hR, bot_inf_eq]
  have hI (i : Fin n) : I i.succ = I i.castSucc ∨
      IsCyclicPrimeStep TP (I i.succ) (I i.castSucc) :=
    intersect_primeStep TP M (R i.succ) (R i.castSucc)
      (rebase_primeStep F T _ _ (hs i))
  obtain ⟨m, S, h₀, hl, hS, hmem⟩ := compress_chain (IsCyclicPrimeStep TP) I hI
  refine ⟨m, S, (congrArg (fun Z : Extension TP => Z.field) h₀).trans ht,
    (congrArg (fun Z : Extension TP => Z.field) hl).trans hb', hS, ?_⟩
  intro k b
  obtain ⟨l, hl⟩ := hmem k
  rw [hl]
  exact projected_constituent_irreducible F E T C a χ η hC hη (tower l) (hT l) b
    (hirr l (j b * a))

end Langlands.Global.GeneralPosition
