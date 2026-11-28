import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.RootSystem.Defs

/-! # Coroot scales and divided roots for covering data -/

namespace Langlands.Covering.Dual

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable (P : RootDatum ι X Y) (Q : QuadraticForm ℤ Y)

/-- Weissman's polarization identity, using the invariance at the given root index. -/
theorem polarBilin_coroot (i : ι) (hQ : ∀ y : Y, Q (P.coreflection i y) = Q y) (y : Y) :
    Q.polarBilin (P.coroot i) y = Q (P.coroot i) * P.root' i y := by
  have hPolar :
      QuadraticMap.polar Q (P.coreflection i (P.coroot i)) (P.coreflection i y) =
        QuadraticMap.polar Q (P.coroot i) y := by
    simp only [QuadraticMap.polar, ← map_add, hQ]
  rw [P.coreflection_apply_self i, P.coreflection_apply i y, QuadraticMap.polar_neg_left,
    QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_self,
    two_nsmul, Int.zsmul_eq_mul, mul_add] at hPolar
  rw [QuadraticMap.polarBilin_apply_apply, mul_comm (Q (P.coroot i))]
  omega

/-- The scale `n / gcd(n, Q(αᵢ∨))` on the coroot at index `i`. -/
def corootScale (n : ℤ) (i : ι) : ℤ :=
  n / (Int.gcd n (Q (P.coroot i)) : ℤ)

private theorem degree_gcd_pos {n : ℤ} (hn : 0 < n) (q : ℤ) :
    (0 : ℤ) < (Int.gcd n q : ℤ) :=
  Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_left q hn.ne')

theorem corootScale_pos (n : ℤ) (hn : 0 < n) (i : ι) :
    0 < corootScale P Q n i := by
  have hle : 1 ≤ corootScale P Q n i := by
    unfold corootScale
    apply (Int.le_ediv_iff_mul_le (degree_gcd_pos hn (Q (P.coroot i)))).2
    rw [one_mul]
    exact Int.le_of_dvd hn (Int.gcd_dvd_left _ _)
  exact lt_of_lt_of_le Int.zero_lt_one hle

theorem degree_dvd_mul_coroot_value_iff (n : ℤ) (hn : 0 < n) (i : ι) (k : ℤ) :
    n ∣ k * Q (P.coroot i) ↔ corootScale P Q n i ∣ k := by
  rw [corootScale, Int.ediv_dvd_iff_dvd_mul (Int.gcd_dvd_left _ _)
    (degree_gcd_pos hn (Q (P.coroot i))).ne', Int.coe_gcd, dvd_gcd_mul_iff_dvd_mul,
    mul_comm k (Q (P.coroot i))]

theorem corootScale_eq_one_of_coroot_value_eq_zero (n : ℤ) (hn : 0 < n) (i : ι)
    (h : Q (P.coroot i) = 0) : corootScale P Q n i = 1 := by
  rw [corootScale, h, Int.gcd_zero_right, Int.natAbs_of_nonneg hn.le, Int.ediv_self hn.ne']

theorem corootScale_neg (n : ℤ) (i : ι) :
    corootScale P (-Q) n i = corootScale P Q n i := by
  simp only [corootScale, neg_apply, Int.coe_gcd, gcd_neg]

theorem corootScale_reflectionPerm (n : ℤ) (j : ι)
    (hQ : ∀ y : Y, Q (P.coreflection j y) = Q y) (i : ι) :
    corootScale P Q n (P.reflectionPerm j i) = corootScale P Q n i := by
  rw [corootScale, corootScale, P.coroot_reflectionPerm, hQ]

/-- The original coroot multiplied by its covering scale in the cocharacter module. -/
def scaledCoroot (n : ℤ) (i : ι) : Y :=
  corootScale P Q n i • P.coroot i

theorem degree_dvd_polarBilin_scaledCoroot (n : ℤ) (hn : 0 < n) (i : ι)
    (hQ : ∀ y : Y, Q (P.coreflection i y) = Q y) (y : Y) :
    n ∣ Q.polarBilin (scaledCoroot P Q n i) y := by
  rw [scaledCoroot, map_smul, LinearMap.smul_apply, Int.zsmul_eq_mul,
    polarBilin_coroot P Q i hQ, ← mul_assoc]
  exact dvd_mul_of_dvd_left ((degree_dvd_mul_coroot_value_iff P Q n hn i _).2 dvd_rfl) _

theorem corootScale_dvd_root_apply (n : ℤ) (hn : 0 < n) (i : ι)
    (hQ : ∀ y : Y, Q (P.coreflection i y) = Q y) {y : Y}
    (hy : n ∣ Q.polarBilin y (P.coroot i)) :
    corootScale P Q n i ∣ P.root' i y := by
  have hsym : Q.polarBilin y (P.coroot i) = Q.polarBilin (P.coroot i) y := by
    simpa only [QuadraticMap.polarBilin_apply_apply] using
      QuadraticMap.polar_comm Q y (P.coroot i)
  rw [hsym, polarBilin_coroot P Q i hQ, mul_comm] at hy
  exact (degree_dvd_mul_coroot_value_iff P Q n hn i _).1 hy

section DividedRoot

variable (n : ℤ) (hn : 0 < n) (i : ι) (hQ : ∀ y : Y, Q (P.coreflection i y) = Q y)
variable (L : Submodule ℤ Y) (hL : ∀ y : L, n ∣ Q.polarBilin (y : Y) (P.coroot i))

/-- Integral root evaluation divided by the coroot scale on a submodule satisfying
the polarization congruence at this coroot. -/
def dividedRoot : L →ₗ[ℤ] ℤ := by
  let scale := corootScale P Q n i
  have hquot (y : L) : scale * (P.root' i (y : Y) / scale) = P.root' i (y : Y) :=
    Int.mul_ediv_cancel' (corootScale_dvd_root_apply P Q n hn i hQ (hL y))
  refine
    { toFun := fun y => P.root' i (y : Y) / scale
      map_add' := ?_
      map_smul' := ?_ }
  · intro y z
    apply mul_left_cancel₀ (corootScale_pos P Q n hn i).ne'
    change scale * (P.root' i (↑(y + z)) / scale) =
      scale * (P.root' i (y : Y) / scale + P.root' i (z : Y) / scale)
    rw [hquot (y + z), mul_add, hquot y, hquot z]
    exact map_add (P.root' i) (y : Y) (z : Y)
  · intro r y
    apply mul_left_cancel₀ (corootScale_pos P Q n hn i).ne'
    change scale * (P.root' i (↑(r • y)) / scale) =
      scale * (r * (P.root' i (y : Y) / scale))
    rw [hquot (r • y), mul_left_comm scale r, hquot y]
    exact map_smul (P.root' i) r (y : Y)

theorem dividedRoot_apply (y : L) :
    dividedRoot P Q n hn i hQ L hL y = P.root' i (y : Y) / corootScale P Q n i :=
  rfl

theorem mul_dividedRoot_apply (y : L) :
    corootScale P Q n i * dividedRoot P Q n hn i hQ L hL y = P.root' i (y : Y) :=
  Int.mul_ediv_cancel' (corootScale_dvd_root_apply P Q n hn i hQ (hL y))

theorem sub_dividedRoot_smul_scaledCoroot (y : L) :
    (y : Y) - dividedRoot P Q n hn i hQ L hL y • scaledCoroot P Q n i =
      P.coreflection i (y : Y) := by
  rw [scaledCoroot, smul_smul, mul_comm _ (corootScale P Q n i),
    mul_dividedRoot_apply, P.coreflection_apply]

theorem dividedRoot_scaledCoroot (hmem : scaledCoroot P Q n i ∈ L) :
    dividedRoot P Q n hn i hQ L hL ⟨scaledCoroot P Q n i, hmem⟩ = 2 := by
  apply mul_left_cancel₀ (corootScale_pos P Q n hn i).ne'
  rw [mul_dividedRoot_apply]
  change P.root' i (corootScale P Q n i • P.coroot i) = corootScale P Q n i * 2
  rw [map_smul, P.root'_coroot_eq_pairing, P.pairing_same, Int.zsmul_eq_mul]

end DividedRoot

end Langlands.Covering.Dual
