import Langlands.Representation.Jacquet.JointIwahoriEigenCoefficient
import Langlands.Representation.Jacquet.IwahoriCellVolume

/-! # Square integrability bounds Jacquet eigenvalues along weak contractions

A smooth coefficient which is `L²` on the central quotient and equal to
`μ ^ n * ν` on the cells `K h(n) K` forces `weight * |μ|² < 1` when the cells are
disjoint with volumes at least `weight ^ n` times a positive constant. Combined
with the joint eigen-coefficient and the Iwahori double-coset volumes for the
elements `a ^ n * b`, this bounds the Jacquet eigenvalue of a weakly contracting
element `a` by the Iwahori index of `a`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace Langlands.Jacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem isOpen_centralCell (K : OpenSubgroup G) (g : G) : IsOpen (centralCell K g) := by
  apply QuotientGroup.isOpenMap_coe
  change IsOpen ((K : Set G) * {g} * (K : Set G))
  exact K.isOpen.mul_left

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (haar : Measure (G ⧸ Subgroup.center G)) [haar.IsHaarMeasure]

omit [haar.IsHaarMeasure] in
/-- `L²` integrability of a coefficient equal to `μ ^ n * ν` on disjoint cells
`K h(n) K` with volumes at least `weight ^ n * C` forces `weight * |μ|² < 1`. -/
theorem weight_mul_enorm_sq_lt_one_of_memLp_cells
    (ρ : Representation ℂ G V) (c : UnitaryCentralCharacter ρ)
    (K : OpenSubgroup G) (h : ℕ → G) (weight C : ℝ≥0∞) (hC : C ≠ 0)
    (hdisj : Pairwise (Function.onFun Disjoint fun n => centralCell K (h n)))
    (hvol : ∀ n, weight ^ n * C ≤ haar (centralCell K (h n)))
    (x : fixedVectors ρ K.toSubgroup) (ℓ : Module.Dual ℂ V)
    (hℓK : ∀ k ∈ K, ∀ y, ℓ (ρ k y) = ℓ y)
    (μ ν : ℂ) (hν : ν ≠ 0) (hcoef : ∀ n : ℕ, ℓ (ρ (h n) x) = μ ^ n * ν)
    (hL2 : MemLp (c.coefficientNorm ℓ x) 2 haar) :
    weight * ‖μ‖ₑ ^ 2 < 1 := by
  have hcell : ∀ n a, a ∈ DoubleCoset.doubleCoset (h n) K K →
      matrixCoefficient ρ ℓ x a = μ ^ n * ν := by
    intro n a ha
    obtain ⟨u, hu, k, hk, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ha
    have hxk : ρ k (x : V) = x := x.property ⟨k, hk⟩
    change ℓ (ρ (u * h n * k) x) = _
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hxk, hℓK u hu]
    exact hcoef n
  have hsum := countableCellLpLower (G ⧸ Subgroup.center G) ℕ haar
    (c.coefficientNorm ℓ x) 2 (by norm_num) (by norm_num) hL2
    (fun n => centralCell K (h n))
    (fun n => (isOpen_centralCell K (h n)).measurableSet)
    hdisj (fun n => ‖μ ^ n * ν‖ₑ) (by
      rintro n q ⟨a, ha, rfl⟩
      rw [UnitaryCentralCharacter.coefficientNorm_mk, hcell n a ha, enorm_norm])
  let C' : ℝ≥0∞ := ‖ν‖ₑ ^ 2 * C
  have hC' : C' ≠ 0 := mul_ne_zero (pow_ne_zero _ (enorm_ne_zero.mpr hν)) hC
  have hterm : ∀ n : ℕ,
      (weight * ‖μ‖ₑ ^ 2) ^ n * C' ≤
        ‖μ ^ n * ν‖ₑ ^ (2 : ℝ≥0∞).toReal * haar (centralCell K (h n)) := by
    intro n
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_mul, enorm_pow]
    calc
      _ = (‖μ‖ₑ ^ n * ‖ν‖ₑ) ^ 2 * (weight ^ n * C) := by
        dsimp [C']
        ring
      _ ≤ _ := by
        gcongr
        exact hvol n
  have hfinite : (∑' n : ℕ, (weight * ‖μ‖ₑ ^ 2) ^ n * C') < ∞ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm) hsum
  by_contra hnot
  have hge : 1 ≤ weight * ‖μ‖ₑ ^ 2 := le_of_not_gt hnot
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    tsub_eq_zero_iff_le.mpr hge, ENNReal.inv_zero, ENNReal.top_mul hC'] at hfinite
  exact (lt_irrefl _) hfinite

/-- **Eigenvalue bound along a weak contraction.** Let `K` be compact open with an
Iwahori factorization, `b` an Iwahori contraction and `a` a commuting weak Iwahori
contraction, both central in `M`, and assume unique `Nbar * M * N` factorization
and that the full center lies in `M`. If every `K`-fixed smooth coefficient of `ρ`
is `L²` on the central quotient, and the `K ∩ M`-invariants of the Jacquet module
contain a common eigenvector of `a` and `b` with eigenvalues `μa`, `μb`, then
`[K ∩ N : a (K ∩ N) a⁻¹] * |μa|² < 1`, provided this Iwahori index exceeds one. -/
theorem iwahoriIndex_mul_enorm_sq_lt_one
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (c : UnitaryCentralCharacter ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (N M Nbar : Subgroup G) (hN : IsClosed (N : Set G))
    (hMN : M ≤ Subgroup.normalizer (N : Set G))
    (hMNbar : M ≤ Subgroup.normalizer (Nbar : Set G))
    (hunique : ∀ l ∈ Nbar, ∀ m ∈ M, ∀ u ∈ N, ∀ l' ∈ Nbar, ∀ m' ∈ M, ∀ u' ∈ N,
      l * m * u = l' * m' * u' → l = l' ∧ m = m' ∧ u = u')
    (hZ : Subgroup.center G ≤ M)
    (b a : G) (hb : IsIwahoriContraction K N M Nbar b)
    (ha : IsWeakIwahoriContraction K N M Nbar a) (hab : Commute a b)
    (hbcomm : ∀ m ∈ M, m * b = b * m) (hacomm : ∀ m ∈ M, m * a = a * m)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup))
    (μb μa : ℂ) (w : Coinvariants ρ N) (hw0 : w ≠ 0)
    (hwK : w ∈ fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))
    (hwb : action ρ N M hMN ⟨b, hb.mem_levi⟩ w = μb • w)
    (hwa : action ρ N M hMN ⟨a, ha.mem_levi⟩ w = μa • w)
    (hda : 1 < iwahoriIndex K N a)
    (hL2 : ∀ (ℓ : SmoothDual ρ) (v : V), MemLp (c.coefficientNorm ℓ v) 2 haar) :
    (iwahoriIndex K N a : ℝ≥0∞) * ‖μa‖ₑ ^ 2 < 1 := by
  have hbw := hb.isWeakIwahoriContraction
  obtain ⟨x, ℓ, hℓx, hℓK, hcoef⟩ :=
    exists_joint_eigen_coefficient_of_jacquet_eigenvector ρ hρ K hK N M Nbar hMN b a
      hb ha hab hfin μb μa w hw0 hwK hwb hwa
  have hμb : μb ≠ 0 := by
    intro h0
    apply hw0
    have h1 := congrArg (action ρ N M hMN (⟨b, hb.mem_levi⟩ : M)⁻¹) hwb
    rw [h0, zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] at h1
    exact h1
  have hopenK : IsOpen (QuotientGroup.mk '' (K : Set G) : Set (G ⧸ Subgroup.center G)) :=
    QuotientGroup.isOpenMap_coe _ K.isOpen
  let hK0 := haar (QuotientGroup.mk '' (K : Set G))
  have hK0pos : hK0 ≠ 0 :=
    (hopenK.measure_pos haar ⟨_, Set.mem_image_of_mem _ K.one_mem⟩).ne'
  have hK0top : hK0 ≠ ∞ :=
    ((hK.image continuous_quotient_mk').measure_lt_top).ne
  have hvol : ∀ n : ℕ, haar (centralCell K (a ^ n * b)) =
      (iwahoriIndex K N a : ℝ≥0∞) ^ n * ((iwahoriIndex K N b : ℝ≥0∞) * hK0) := by
    intro n
    have hy : IsWeakIwahoriContraction K N M Nbar (a ^ n * b) := (ha.pow n).mul hbw
    rw [measure_centralCell haar hb.factor hunique hZ hMN hMNbar
      (fun m hm => by
        rw [show m * (a ^ n * b) = (m * a ^ n) * b by group,
          (Commute.pow_right (hacomm m hm) n).eq, mul_assoc, hbcomm m hm, ← mul_assoc])
      hK hN hy, iwahoriIndex_pow_mul ha hbw n]
    push_cast
    ring
  have hdb : iwahoriIndex K N b ≠ 0 := by
    have := finite_quotient_conjRadicalPiece hK hN hMN hbw
    have hfi : ((conjRadicalPiece K N b).subgroupOf (K.toSubgroup ⊓ N)).FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    exact hfi.index_ne_zero
  have hC : (iwahoriIndex K N b : ℝ≥0∞) * hK0 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hdb) hK0pos
  have hCtop : (iwahoriIndex K N b : ℝ≥0∞) * hK0 ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hK0top
  have hdisj : Pairwise (Function.onFun Disjoint fun n => centralCell K (a ^ n * b)) := by
    intro m n hmn
    by_contra hnd
    have heq := centralCell_eq_of_not_disjoint hnd
    have hmeas := congrArg haar heq
    rw [hvol m, hvol n] at hmeas
    have hpow : (iwahoriIndex K N a : ℝ≥0∞) ^ m = (iwahoriIndex K N a : ℝ≥0∞) ^ n :=
      (ENNReal.mul_left_inj hC hCtop).mp hmeas
    have hpow' : iwahoriIndex K N a ^ m = iwahoriIndex K N a ^ n := by exact_mod_cast hpow
    exact hmn (Nat.pow_right_injective hda hpow')
  apply weight_mul_enorm_sq_lt_one_of_memLp_cells haar ρ c K (fun n => a ^ n * b)
    (iwahoriIndex K N a) ((iwahoriIndex K N b : ℝ≥0∞) * hK0) hC hdisj
    (fun n => (hvol n).symm.le) x (ℓ : Module.Dual ℂ V) hℓK μa (μb * (ℓ : Module.Dual ℂ V) x)
    (mul_ne_zero hμb hℓx)
  · intro n
    have h1 := hcoef n 1
    rw [pow_one, pow_one] at h1
    rw [h1, mul_assoc]
  · exact hL2 ℓ x

end Langlands.Jacquet
