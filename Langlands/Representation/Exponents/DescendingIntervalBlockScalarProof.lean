import Langlands.Representation.Exponents.DescendingIntervalBlockScalarStatement

/-! # Descending interval block tensor scalar action and norm -/

noncomputable section

namespace Langlands

open scoped BigOperators

universe uF uV

namespace Classification

/-- The descending interval `(m - 1 - K) + ⋯ + (m - K - k)` of natural endpoints,
summed in the real numbers, when the interval fits below `m`. -/
theorem sum_descending_interval_real (m K k : ℕ) (h : K + k ≤ m) :
    ∑ j : Fin k, ((m - 1 - (K + (j : ℕ)) : ℕ) : ℝ) =
      (k : ℝ) * (((2 * (m : ℝ) - (k : ℝ) - 1) / 2) - (K : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), Nat.cast_sub (by omega : K + k ≤ m - 1),
      Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring

/-- A prefix sum together with the current term is at most the total sum. -/
theorem prefix_add_le_sum {b : ℕ} (k : Fin b → ℕ) (i : Fin b) :
    (∑ j : Fin b with j < i, k j) + k i ≤ ∑ j, k j := by
  classical
  have hi : i ∉ Finset.univ.filter (fun j : Fin b => j < i) := by simp
  rw [add_comm, ← Finset.sum_insert hi]
  exact Finset.sum_le_sum_of_subset (by simp)

end Classification

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type*) [CommRing R]
variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

/-- If each block factor `σ i` has scalar character `c i`, then the block tensor
has the product of the coordinate characters on the split centre. -/
theorem hasScalarCharacter_blockTensor_splitCentre
    {σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) R) (V i)}
    {c : Fin B.length → (Rˣ →* ℂˣ)}
    (h : ∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (c i)) :
    Classification.HasScalarCharacter (B.blockTensor σ) (B.blockScalarLevi R)
      (∏ i, (c i).comp (Pi.evalMonoidHom (fun _ : Fin B.length => Rˣ) i)) := by
  intro a v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have hf : (fun i => σ i (B.blockScalarLevi R a i) (f i)) =
        fun i => (c i (a i) : ℂ) • f i :=
      funext fun i => h i (a i) (f i)
    rw [map_smul, B.blockTensor_tprod, hf, MultilinearMap.map_smul_univ, smul_comm r,
      MonoidHom.finsetProd_apply, Units.coe_prod]
    rfl
  | add x y hx hy =>
    rw [map_add, hx, hy, smul_add]

end GeneralLinear.BlockShape

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The norm of a finite product of twisted scalar characters `ω ⊗ |det|^(e j)`. -/
theorem norm_prod_twistedScalarCharacter (ω : F.Carrierˣ →* ℂˣ)
    (r k : ℕ) (e : Fin k → ℝ) (a : F.Carrierˣ) :
    ‖((∏ j : Fin k,
      (ω * (T.determinantPowerCharacter r (e j)).comp GeneralLinear.scalar)) a : ℂ)‖ =
      ‖(ω a : ℂ)‖ ^ k *
        T.normalizedAbs (a : F.Carrier) ^ ((r : ℝ) * ∑ j, e j) := by
  have hpos := T.normalizedAbs_pos a.ne_zero
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  simp only [MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, norm_mul,
    T.norm_determinantPowerCharacter_scalar]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.rpow_sum_of_pos hpos, ← Finset.mul_sum]

/-- The norm of the descending-interval character of one block. -/
theorem norm_prod_descendingIntervalScalarCharacter (ω : F.Carrierˣ →* ℂˣ)
    (r m K k : ℕ) (h : K + k ≤ m) (a : F.Carrierˣ) :
    ‖((∏ j : Fin k,
      (ω * (T.determinantPowerCharacter r
        ((m - 1 - (K + (j : ℕ)) : ℕ) : ℝ)).comp GeneralLinear.scalar)) a : ℂ)‖ =
      ‖(ω a : ℂ)‖ ^ k *
        T.normalizedAbs (a : F.Carrier) ^
          ((r : ℝ) * (k : ℝ) *
            (((2 * (m : ℝ) - (k : ℝ) - 1) / 2) - (K : ℝ))) := by
  rw [T.norm_prod_twistedScalarCharacter,
    Classification.sum_descending_interval_real m K k h, mul_assoc]

/-- The norm of the split-centre character of descending intervals on all blocks. -/
theorem norm_prod_blockDescendingIntervalScalarCharacter {b : ℕ}
    (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (k : Fin b → ℕ)
    (hk : ∑ i, k i = m) (a : Fin b → F.Carrierˣ) :
    let K : Fin b → ℕ := fun i => ∑ j : Fin b with j < i, k j
    let c : Fin b → (F.Carrierˣ →* ℂˣ) := fun i =>
      ∏ j : Fin (k i), ω * (T.determinantPowerCharacter r
        ((m - 1 - (K i + (j : ℕ)) : ℕ) : ℝ)).comp GeneralLinear.scalar
    ‖((∏ i, (c i).comp (Pi.evalMonoidHom (fun _ : Fin b => F.Carrierˣ) i)) a : ℂ)‖ =
      ∏ i, (‖(ω (a i) : ℂ)‖ ^ k i *
        T.normalizedAbs (a i : F.Carrier) ^
          ((r : ℝ) * (k i : ℝ) *
            (((2 * (m : ℝ) - (k i : ℝ) - 1) / 2) -
              ((∑ j : Fin b with j < i, k j : ℕ) : ℝ)))) := by
  dsimp only
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [MonoidHom.comp_apply, Pi.evalMonoidHom_apply] using
    T.norm_prod_descendingIntervalScalarCharacter ω r m _ (k i)
    ((Classification.prefix_add_le_sum k i).trans_eq hk) (a i)

end PadicField.TopologicalData

/-- The exact scalar-action and descending-interval norm proposition. -/
theorem descendingIntervalBlockScalarFormula {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    DescendingIntervalBlockScalarFormula.{uF,uV} F T := by
  intro n B V _ _ σ ω r m k hk
  dsimp only
  intro hσ
  exact ⟨B.hasScalarCharacter_blockTensor_splitCentre F.Carrier hσ,
    T.norm_prod_blockDescendingIntervalScalarCharacter ω r m k hk⟩

end Langlands
