import Langlands.Representation.Archimedean.RealLeviModes

/-! # Removal of low rotation Fourier modes in real compact pictures -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

open RealBlockFourierFinite RealBlockJacquet RealBlockRotation RealInducedBlockBound

local notation "G" => Langlands.GeneralLinear

variable {n : ℕ}

/-- The integral modes with absolute value strictly below the cutoff. -/
def lowModes (m : ℕ) : Finset ℤ := Finset.Ioo (-(m : ℤ)) (m : ℤ)

@[simp]
theorem mem_lowModes {m : ℕ} {j : ℤ} : j ∈ lowModes m ↔ |j| < (m : ℤ) := by
  rw [lowModes, Finset.mem_Ioo, abs_lt]

/-- The block rotation coefficient as a linear map on continuous functions. -/
def coefficientMap (p : ℕ) (j : ℤ) : Module.End ℂ C(G n ℝ, ℂ) where
  toFun f := ⟨blockFourierCoefficient n p j f, continuous_blockFourierCoefficient p j f.continuous⟩
  map_add' f h := ContinuousMap.ext fun x =>
    blockFourierCoefficient_add p j f.continuous h.continuous x
  map_smul' a f := ContinuousMap.ext fun x => blockFourierCoefficient_smul p j a f x

@[simp]
theorem coefficientMap_apply (p : ℕ) (j : ℤ) (f : C(G n ℝ, ℂ)) (x : G n ℝ) :
    coefficientMap p j f x = blockFourierCoefficient n p j f x := rfl

private theorem coefficientMap_coefficientMap {p : ℕ} (hp : p + 1 < n) (j l : ℤ)
    (f : C(G n ℝ, ℂ)) :
    coefficientMap p j (coefficientMap p l f) =
      if l = j then (2 * (Real.pi : ℂ)) • coefficientMap p j f else 0 := by
  apply ContinuousMap.ext
  intro x
  rw [coefficientMap_apply, blockFourierCoefficient_eq_coeff]
  have he : (fun θ => coefficientMap p l f (blockRotation n p θ * x)) =
      coefficientMap p l f x • expMode l := by
    funext θ
    simp only [coefficientMap_apply, Pi.smul_apply, smul_eq_mul, expMode,
      blockFourierCoefficient_blockRotation_mul hp, mul_comm]
  rw [he, coeff_smul, coeff_expMode]
  split_ifs with h
  · subst l
    change _ = (2 * (Real.pi : ℂ)) * coefficientMap p j f x
    exact mul_comm _ _
  · simp

/-- Remove the normalized Fourier modes of absolute value strictly below `m`. -/
def highModes (p m : ℕ) : Module.End ℂ C(G n ℝ, ℂ) :=
  LinearMap.id - (2 * (Real.pi : ℂ))⁻¹ • ∑ j ∈ lowModes m, coefficientMap p j

theorem highModes_apply (p m : ℕ) (f : C(G n ℝ, ℂ)) :
    highModes p m f =
      f - (2 * (Real.pi : ℂ))⁻¹ • ∑ j ∈ lowModes m, coefficientMap p j f := by
  simp only [highModes, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    LinearMap.sum_apply]

/-- The low modes of the chosen rotation vanish after applying the filter. -/
theorem coefficientMap_highModes_self {p m : ℕ} (hp : p + 1 < n) {j : ℤ}
    (hj : j ∈ lowModes m) (f : C(G n ℝ, ℂ)) :
    coefficientMap p j (highModes p m f) = 0 := by
  simp only [highModes_apply, map_sub, map_smul, map_sum, coefficientMap_coefficientMap hp]
  rw [Finset.sum_ite_eq', ite_eq_left hj, smul_smul, inv_mul_cancel₀, one_smul, sub_self]
  exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)

private theorem coefficientMap_comm {p q : ℕ} (hpq : p + 1 < q ∨ q + 1 < p)
    (j l : ℤ) (f : C(G n ℝ, ℂ)) :
    coefficientMap p j (coefficientMap q l f) = coefficientMap q l (coefficientMap p j f) :=
  ContinuousMap.ext fun x => blockFourierCoefficient_comm hpq f.continuous j l x

theorem coefficientMap_highModes_comm {p q m : ℕ} (hpq : p + 1 < q ∨ q + 1 < p)
    (j : ℤ) (f : C(G n ℝ, ℂ)) :
    coefficientMap p j (highModes q m f) = highModes q m (coefficientMap p j f) := by
  simp only [highModes_apply, map_sub, map_smul, map_sum, coefficientMap_comm hpq]

/-- Apply the high-mode filters at a list of rotation blocks. -/
def highModesList (S : List (Slot n)) : Module.End ℂ C(G n ℝ, ℂ) :=
  S.foldr (fun s A => (highModes s.p s.M).comp A) LinearMap.id

@[simp]
theorem highModesList_nil (f : C(G n ℝ, ℂ)) :
    highModesList ([] : List (Slot n)) f = f := rfl

@[simp]
theorem highModesList_cons (s : Slot n) (S : List (Slot n)) (f : C(G n ℝ, ℂ)) :
    highModesList (s :: S) f = highModes s.p s.M (highModesList S f) := rfl

theorem coefficientMap_highModesList_eq_zero {S : List (Slot n)} (hS : S.Pairwise Slot.Disjoint)
    {s : Slot n} (hs : s ∈ S) {j : ℤ} (hj : j ∈ lowModes s.M) (f : C(G n ℝ, ℂ)) :
    coefficientMap s.p j (highModesList S f) = 0 := by
  induction S with
  | nil => simp at hs
  | cons t S ih =>
    obtain ⟨ht, hS'⟩ := List.pairwise_cons.mp hS
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact coefficientMap_highModes_self s.hp hj _
    · rw [highModesList_cons, coefficientMap_highModes_comm (ht s hs').symm,
        ih hS' hs', map_zero]

theorem highModesList_eq_of_vanishing {S : List (Slot n)} (f : C(G n ℝ, ℂ))
    (hf : ∀ s ∈ S, ∀ j ∈ lowModes s.M, coefficientMap s.p j f = 0) :
    highModesList S f = f := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    rw [highModesList_cons, ih (fun t ht => hf t (List.mem_cons_of_mem s ht)), highModes_apply]
    rw [show (∑ j ∈ lowModes s.M, coefficientMap s.p j f) = 0 from
      Finset.sum_eq_zero (hf s List.mem_cons_self)]
    apply ContinuousMap.ext
    intro x
    change f x - (2 * (Real.pi : ℂ))⁻¹ * 0 = f x
    simp

theorem highModes_isKFin {p m : ℕ} {f : C(G n ℝ, ℂ)} (hf : IsKFin f) :
    IsKFin (highModes p m f) := by
  rw [highModes_apply]
  change ContinuousMap.coeFnLinearMap ℂ
    (f - (2 * (Real.pi : ℂ))⁻¹ • ∑ j ∈ lowModes m, coefficientMap p j f) ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (G n ℝ)) (unitaryCompact ℝ n)
  simp only [map_sub, map_smul, map_sum]
  refine Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_))
  exact isKFin_blockFourierCoefficient f.continuous hf p j

theorem highModesList_isKFin (S : List (Slot n)) {f : C(G n ℝ, ℂ)} (hf : IsKFin f) :
    IsKFin (highModesList S f) := by
  induction S with
  | nil => exact hf
  | cons s S ih => exact highModes_isKFin ih

theorem highModes_apply_at (p m : ℕ) (f : C(G n ℝ, ℂ)) (x : G n ℝ) :
    highModes p m f x = f x - (2 * (Real.pi : ℂ))⁻¹ *
      ∑ j ∈ lowModes m, blockFourierCoefficient n p j f x := by
  let E : C(G n ℝ, ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ x
  change E (highModes p m f) = _
  simp only [highModes_apply, map_sub, map_smul, map_sum]
  rfl

theorem highModesList_eqOn (S : List (Slot n)) {f h : C(G n ℝ, ℂ)}
    (he : Set.EqOn f h (unitaryCompact ℝ n)) :
    Set.EqOn (highModesList S f) (highModesList S h) (unitaryCompact ℝ n) := by
  induction S with
  | nil => exact he
  | cons s S ih =>
    intro x hx
    simp only [highModesList_cons, highModes_apply_at, ih hx]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold blockFourierCoefficient
    exact intervalIntegral.integral_congr fun θ _ => congrArg (fun z : ℂ => z * _)
      (ih ((unitaryCompact ℝ n).mul_mem (blockRotation_mem_unitaryCompact n s.p θ) hx))

private theorem sum_lowModes_neg (m : ℕ) (a : ℤ → ℂ) :
    ∑ j ∈ lowModes m, a (-j) = ∑ j ∈ lowModes m, a j := by
  refine Finset.sum_nbij' Neg.neg Neg.neg ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  all_goals simp

theorem highModes_signReflection {p m : ℕ} (hp : p + 1 < n) (i : Fin n) (c : ℂ)
    {f : C(G n ℝ, ℂ)} (hf : ∀ x, f (Unitary.toUnits (signReflection n i) * x) = c * f x)
    (x : G n ℝ) :
    highModes p m f (Unitary.toUnits (signReflection n i) * x) = c * highModes p m f x := by
  rw [highModes_apply_at, highModes_apply_at, hf]
  simp_rw [RealLeviModes.blockFourierCoefficient_signReflection_mul hp i hf]
  rw [← Finset.mul_sum]
  split_ifs
  · rw [sum_lowModes_neg m (fun j => blockFourierCoefficient n p j f x)]
    ring
  · ring

theorem highModesList_signReflection (S : List (Slot n)) (i : Fin n) (c : ℂ)
    {f : C(G n ℝ, ℂ)} (hf : ∀ x, f (Unitary.toUnits (signReflection n i) * x) = c * f x)
    (x : G n ℝ) :
    highModesList S f (Unitary.toUnits (signReflection n i) * x) =
      c * highModesList S f x := by
  induction S generalizing x with
  | nil => exact hf x
  | cons s S ih =>
    simp only [highModesList_cons]
    exact highModes_signReflection s.hp i c ih x

/-- Low modes vanish after applying the filters in a list of disjoint blocks. -/
def RealStandardCompactFourierStatement : Prop :=
  ∀ (n : ℕ) (S : List (Slot n)), S.Pairwise Slot.Disjoint →
    ∀ f : C(G n ℝ, ℂ), ∀ s ∈ S, ∀ j ∈ lowModes s.M,
      coefficientMap s.p j (highModesList S f) = 0

theorem realStandardCompactFourier : RealStandardCompactFourierStatement :=
  fun _ _ hS f _ hs _ hj => coefficientMap_highModesList_eq_zero hS hs hj f

end Langlands.Archimedean.RealStandardCompactAverage
