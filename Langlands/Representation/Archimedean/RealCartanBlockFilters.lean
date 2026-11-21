import Langlands.Representation.Archimedean.RealCartanBlockLayout
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Group the compact sign and low-mode projections by original blocks -/

noncomputable section

namespace Langlands.Archimedean.RealCartanBlockFilters

open Langlands.LocalFactor.Archimedean RealLeviChart RealBlockRotation RealBlockFourierFinite
  RealStandardCompactAverage RealCartanFilterSupport RealCartanBlockLayout
  RealInducedStandardBound RealInducedBlockBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "Ops" n:max => Module.End ℂ C(G n, ℂ)

section Operators

variable {n : ℕ}

private def pullLeft (a : G n) : Ops n :=
  (ContinuousMap.compCLM ℂ ℂ ⟨fun x => a * x, continuous_const.mul continuous_id⟩).toLinearMap

@[simp]
private theorem pullLeft_apply (a : G n) (f : C(G n, ℂ)) (x : G n) : pullLeft a f x = f (a * x) := rfl

private theorem signFilter_eq (ds : List RealBlock) (i : Fin n) :
    signFilter ds i = (2 : ℂ)⁻¹ • (1 + realPositionCharacter ds i (-1) •
      pullLeft (Unitary.toUnits (signReflection n i))) := by
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  rfl

private theorem signFilter_commute (ds : List RealBlock) (i j : Fin n) :
    Commute (signFilter ds i) (signFilter ds j) := by
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  let a := Unitary.toUnits (signReflection n i)
  let b := Unitary.toUnits (signReflection n j)
  have h : b * (a * x) = a * (b * x) := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, signReflection_mul_comm]
  change signFilter ds i (signFilter ds j f) x = signFilter ds j (signFilter ds i f) x
  simp only [signFilter_apply]
  change (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (f x + realPositionCharacter ds j (-1) * f (b * x)) +
    realPositionCharacter ds i (-1) * ((2 : ℂ)⁻¹ * (f (a * x) +
      realPositionCharacter ds j (-1) * f (b * (a * x))))) = _
  rw [h]
  ring

private theorem coefficientMap_commute_pullLeft {p : ℕ} (j : ℤ) (a : G n)
    (ha : ∀ θ, Commute (blockRotation n p θ) a) :
    Commute (coefficientMap p j) (pullLeft a) := by
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  change coefficientMap p j (pullLeft a f) x = pullLeft a (coefficientMap p j f) x
  simp only [coefficientMap_apply, pullLeft_apply, blockFourierCoefficient]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [← mul_assoc, (ha θ).eq]

private theorem lowProjection_commute_signFilter (ds : List RealBlock) (s : Slot n)
    (i : Fin n) (hi : (i : ℕ) ≠ s.p ∧ (i : ℕ) ≠ s.p + 1) :
    Commute (lowProjection s) (signFilter ds i) := by
  let a := Unitary.toUnits (signReflection n i)
  have ha (θ : ℝ) : Commute (blockRotation n s.p θ) a := by
    have hs := signReflection_mul_blockRotation_mul_of_not_mem s.hp i hi θ
    have h : a * (blockRotation n s.p θ * a) = blockRotation n s.p θ := by
      simpa only [mul_assoc] using hs
    change blockRotation n s.p θ * a = a * blockRotation n s.p θ
    calc
      _ = a * (a * (blockRotation n s.p θ * a)) := by
        simp only [a, toUnits_signReflection_mul_mul_self]
      _ = _ := by rw [h]
  rw [signFilter_eq, lowProjection]
  apply Commute.smul_left
  apply Commute.sum_left
  intro j _
  apply Commute.smul_right
  exact (Commute.one_right _).add_right ((coefficientMap_commute_pullLeft j a ha).smul_right _)

private theorem lowProjection_commute {s t : Slot n} (h : Slot.Disjoint s t) :
    Commute (lowProjection s) (lowProjection t) := by
  unfold lowProjection
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sum_left
  intro j _
  apply Commute.sum_right
  intro l _
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  exact blockFourierCoefficient_comm h f.continuous j l x

private theorem signFilters_eq_prod (ds : List RealBlock) (I : List (Fin n)) :
    signFilters ds I = (I.map (signFilter ds)).prod := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    change (signFilter ds i) * signFilters ds I = _
    rw [ih, List.map_cons, List.prod_cons]

private theorem lowProjections_eq_prod (S : List (Slot n)) :
    lowProjections S = (S.map lowProjection).prod := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    change (lowProjection s) * lowProjections S = _
    rw [ih, List.map_cons, List.prod_cons]

end Operators

section Blocks

variable {c : ℕ} (b : Fin c → RealBlock)

local notation "sz" => blockSizes b
local notation "N" => ∑ i, blockSizes b i
local notation "ds" => List.ofFn b

/-- The coordinate sign projections in one original block. -/
def blockSigns (i : Fin c) : Ops N := signFilters ds (List.ofFn (pos sz i))

/-- The low projection in an induced block, and the identity on a real character block. -/
def blockLow (i : Fin c) : Ops N := (blockSlot b i).elim 1 lowProjection

/-- The compact block operation, with sign projection performed before low modes. -/
def blockFilter (i : Fin c) : Ops N := blockLow b i * blockSigns b i

private theorem signFilters_eq_blockSigns_prod :
    signFilters ds (List.ofFn id) = ((List.finRange c).map (blockSigns b)).prod := by
  let L := List.finRange c
  have h := (positions_perm_blockPositions sz).map (signFilter ds)
  have hcomm : ((List.ofFn id).map (signFilter (n := N) ds)).Pairwise Commute := by
    rw [List.pairwise_map, List.pairwise_ofFn]
    intro i j _
    exact signFilter_commute ds i j
  rw [signFilters_eq_prod, h.prod_eq' hcomm]
  change ((L.flatMap fun i => List.ofFn (pos sz i)).map (signFilter ds)).prod =
    (L.map (blockSigns b)).prod
  induction L with
  | nil => rfl
  | cons i L ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
      blockSigns, signFilters_eq_prod, ih]

private theorem lowProjections_eq_blockLow_prod :
    lowProjections (slots ds N) = ((List.finRange c).map (blockLow b)).prod := by
  let L := List.finRange c
  have h := (slots_perm_blockSlots b).map lowProjection
  have hc : ((slots ds N).map lowProjection).Pairwise Commute :=
    List.pairwise_map.mpr ((pairwise_slots ds N).imp (fun {s t} hst => lowProjection_commute hst))
  rw [lowProjections_eq_prod, h.prod_eq' hc]
  change ((L.filterMap (blockSlot b)).map lowProjection).prod = (L.map (blockLow b)).prod
  induction L with
  | nil => rfl
  | cons i L ih =>
    cases he : blockSlot b i <;> simp [he, blockLow, ih]

private theorem cls_at_slot (i : Fin c) (d : ComplexCharacterData) (hi : b i = .induced d)
    (hp : start sz i + 1 < N) :
    cls sz (ia hp) = i ∧ cls sz (ib hp) = i := by
  let a₀ : Fin (sz i) := ⟨0, blockSizes_pos b i⟩
  let a₁ : Fin (sz i) := ⟨1, by change 1 < (b i).rank; simp [hi, RealBlock.rank]⟩
  have h₀ : ia hp = pos sz i a₀ := Fin.ext (by rw [val_pos]; simp [ia, a₀])
  have h₁ : ib hp = pos sz i a₁ := Fin.ext (by rw [val_pos]; rfl)
  rw [h₀, h₁, cls_pos, cls_pos]
  exact ⟨rfl, rfl⟩

private theorem blockSigns_commute_blockLow {i j : Fin c} (hij : i ≠ j) :
    Commute (blockSigns b i) (blockLow b j) := by
  cases hj : b j with
  | character d =>
    rw [blockLow, blockSlot_character b j d hj]
    exact Commute.one_right _
  | induced d =>
    obtain ⟨hp, hs⟩ := blockSlot_induced b j d hj
    have hc := cls_at_slot b j d hj hp
    rw [blockLow, hs]
    change Commute (signFilters ds (List.ofFn (pos sz i)))
      (lowProjection (mkSlot ds N (start sz j) hp d))
    rw [signFilters_eq_prod]
    apply Commute.list_prod_left
    intro op hop
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hop
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hp'
    apply Commute.symm
    apply lowProjection_commute_signFilter
    refine ⟨fun h => hij ?_, fun h => hij ?_⟩
    · have he : pos sz i a = ia hp := Fin.ext h
      exact (cls_pos _ _ _).symm.trans ((congrArg (cls sz) he).trans hc.1)
    · have he : pos sz i a = ib hp := Fin.ext h
      exact (cls_pos _ _ _).symm.trans ((congrArg (cls sz) he).trans hc.2)

private theorem regroup_filters (L : List (Fin c)) (hL : L.Nodup) :
    (L.map (blockLow b)).prod * (L.map (blockSigns b)).prod = (L.map (blockFilter b)).prod := by
  induction L with
  | nil => simp
  | cons i L ih =>
    obtain ⟨hi, hL'⟩ := List.nodup_cons.mp hL
    have hc : Commute ((L.map (blockLow b)).prod) (blockSigns b i) := by
      apply Commute.list_prod_left
      intro g hg
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
      have hne : i ≠ j := fun h => hi (h.symm ▸ hj)
      exact (blockSigns_commute_blockLow b hne).symm
    simp only [List.map_cons, List.prod_cons, blockFilter]
    rw [mul_assoc, ← mul_assoc ((L.map (blockLow b)).prod), hc.eq,
      mul_assoc (blockSigns b i), ih hL', ← mul_assoc]

/-- The actual compact sign and low projections can be grouped in original block order. -/
def RealCartanBlockFiltersStatement : Prop :=
  ∀ (c : ℕ) (b : Fin c → RealBlock),
    let n := ∑ i, blockSizes b i
    lowProjections (slots (List.ofFn b) n) * signFilters (n := n) (List.ofFn b) (List.ofFn id) =
      ((List.finRange c).map (blockFilter b)).prod

theorem realCartanBlockFilters : RealCartanBlockFiltersStatement := by
  intro c b n
  rw [signFilters_eq_blockSigns_prod b, lowProjections_eq_blockLow_prod b]
  exact regroup_filters b _ (List.nodup_finRange c)

end Blocks

end Langlands.Archimedean.RealCartanBlockFilters
