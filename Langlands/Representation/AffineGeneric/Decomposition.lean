import Langlands.Representation.AffineGeneric.Subgroup
import Langlands.Group.GL.UpperBruhatProof

/-!
# Iwahori units and the decomposition `G = 𝔄ˣ · W · B(F)`

An integral invertible matrix whose reduction modulo the maximal ideal is upper triangular is a
unit of the standard Iwahori order. Combining the Iwasawa decomposition `G = B(F) GL_{m+1}(𝒪)`
with the Bruhat decomposition of `GL_{m+1}(k)` over the residue field, every
`x ∈ GL_{m+1}(F)` is `ι w β b⁻¹` with `ι` a unit of the Iwahori order, `w` a permutation
matrix and `β`, `b` upper triangular.
-/

noncomputable section

namespace Langlands.AffineGeneric

open ValuativeRel Matrix LevelZero GeneralLinear

universe u

variable {F : Type u} [Field F] [ValuativeRel F] {m : ℕ}

/-- Reduction modulo the maximal ideal computes the residues of the entries. -/
theorem resOf_entry (g : Conductor.integralSubgroup (integers F) m) (i j : Fin (m + 1)) :
    resOf ((g : GeneralLinear (m + 1) F) i j) = IntegralReduction.reduction (integers F) m g i j := by
  rw [IntegralReduction.reduction_apply, ← resOf_coe,
    IntegralReduction.integralEquiv_symm_apply_val]

/-- An integral invertible matrix with upper triangular reduction lies in the Iwahori order. -/
theorem isIwahoriOrder_of_reduction (g : Conductor.integralSubgroup (integers F) m)
    (hg : ∀ i j : Fin (m + 1), j < i → IntegralReduction.reduction (integers F) m g i j = 0) :
    IsIwahoriOrder ((g : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
  have hint := ((Conductor.mem_integralSubgroup _ _ _).mp g.2).1
  intro i j
  have hle : valuation F ((g : GeneralLinear (m + 1) F) i j) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp (hint i j)
  refine ⟨hle, fun hji => ?_⟩
  rw [← resOf_eq_zero_iff hle, resOf_entry]
  exact hg i j hji

/-- The inverse of an upper triangular invertible matrix is upper triangular. -/
theorem inv_upperTriangular {K : Type*} [Field K] {n : ℕ} (a : GeneralLinear n K)
    (ha : ∀ i j : Fin n, j < i → a i j = 0) :
    ∀ i j : Fin n, j < i → (a⁻¹ : GeneralLinear n K) i j = 0 := by
  let _ : Invertible (a : Matrix (Fin n) (Fin n) K) := Units.invertible a
  have hb : (a : Matrix (Fin n) (Fin n) K).BlockTriangular id := fun i j h => ha i j h
  have h := Matrix.blockTriangular_inv_of_blockTriangular hb
  intro i j hji
  have he : ((a⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K)⁻¹ := Matrix.coe_units_inv a
  change ((a⁻¹ : GeneralLinear n K) : Matrix (Fin n) (Fin n) K) i j = 0
  rw [he]
  exact h hji

theorem permutation_mem_integralSubgroup (w : Equiv.Perm (Fin (m + 1))) :
    permutation (m + 1) F w ∈ Conductor.integralSubgroup (integers F) m := by
  rw [Conductor.mem_integralSubgroup]
  have h01 : ∀ σ : Equiv.Perm (Fin (m + 1)), ∀ i j,
      permutation (m + 1) F σ i j ∈ integers F := by
    intro σ i j
    rw [permutation_entry]
    split_ifs
    · exact (integers F).one_mem
    · exact (integers F).zero_mem
  refine ⟨h01 w, fun i j => ?_⟩
  rw [permutation_inv]
  exact h01 w⁻¹ i j

theorem reduction_permutation (w : Equiv.Perm (Fin (m + 1))) :
    IntegralReduction.reduction (integers F) m
      ⟨permutation (m + 1) F w, permutation_mem_integralSubgroup w⟩ =
      permutation (m + 1) (Residue F) w := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [← resOf_entry]
  change resOf (permutation (m + 1) F w i j) = permutation (m + 1) (Residue F) w i j
  rw [permutation_entry, permutation_entry]
  split_ifs <;> simp

/-- **Iwahori–Bruhat decomposition.** Every `x ∈ GL_{m+1}(F)` is `ι w β b⁻¹` with `ι` and
`ι⁻¹` in the Iwahori order, `w` a permutation matrix and `β`, `b` upper triangular. -/
theorem exists_iwahori_decomposition (x : GeneralLinear (m + 1) F) :
    ∃ (ι : GeneralLinear (m + 1) F) (w : Equiv.Perm (Fin (m + 1)))
      (β b : GeneralLinear (m + 1) F),
      IsIwahoriOrder (ι : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      IsIwahoriOrder ((ι⁻¹ : GeneralLinear (m + 1) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) ∧
      (∀ i j : Fin (m + 1), j < i → β i j = 0) ∧
      (∀ i j : Fin (m + 1), j < i → b i j = 0) ∧
      x = ι * permutation (m + 1) F w * β * b⁻¹ := by
  classical
  obtain ⟨b, hb, k, hk, hxk⟩ := Iwasawa.exists_upperTriangular_mul (valuation F) x⁻¹
  let κ : Conductor.integralSubgroup (integers F) m := ⟨k⁻¹, inv_mem hk⟩
  obtain ⟨a, bb, w, ha, hbb, hred⟩ := fieldUpperBruhatFactorizationTheorem (Residue F) (m + 1)
    (IntegralReduction.reduction (integers F) m κ)
  let β : Conductor.integralSubgroup (integers F) m := IntegralReduction.lift (integers F) m bb
  let P : Conductor.integralSubgroup (integers F) m :=
    ⟨permutation (m + 1) F w, permutation_mem_integralSubgroup w⟩
  let ι : Conductor.integralSubgroup (integers F) m := κ * β⁻¹ * P⁻¹
  have hredι : IntegralReduction.reduction (integers F) m ι = a := by
    simp only [ι, map_mul, map_inv, hred, P, reduction_permutation, β,
      IntegralReduction.reduction_lift]
    group
  have hredι' : IntegralReduction.reduction (integers F) m ι⁻¹ = a⁻¹ := by
    rw [map_inv, hredι]
  refine ⟨ι, w, β, b, ?_, ?_, ?_, fun i j h => hb h, ?_⟩
  · exact isIwahoriOrder_of_reduction ι (fun i j h => by rw [hredι]; exact ha i j h)
  · exact isIwahoriOrder_of_reduction ι⁻¹
      (fun i j h => by rw [hredι']; exact inv_upperTriangular a ha i j h)
  · intro i j h
    change (IntegralReduction.lift (integers F) m bb : GeneralLinear (m + 1) F) i j = 0
    rw [IntegralReduction.lift_apply, hbb i j h, IntegralReduction.residueSection_zero]
    rfl
  · have hκ : (κ : GeneralLinear (m + 1) F) = (ι : GeneralLinear (m + 1) F) *
        permutation (m + 1) F w * (β : GeneralLinear (m + 1) F) := by
      simp only [ι, Subgroup.coe_mul, Subgroup.coe_inv, P]
      group
    have hx : x = k⁻¹ * b⁻¹ := by
      rw [← _root_.mul_inv_rev, ← hxk, inv_inv]
    rw [hx, show k⁻¹ = (κ : GeneralLinear (m + 1) F) from rfl, hκ]

end Langlands.AffineGeneric
