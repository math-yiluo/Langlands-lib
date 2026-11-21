import Langlands.Algebra.LocalDivisionCyclicBasis
import Langlands.Algebra.CyclicNormCommutator
import Langlands.ClassFieldTheory.Local.LocalUnramifiedNorm

/-! # Norm adjustment of a cyclic division-algebra parameter -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel Langlands.LocalClassField Langlands.ClassFieldTheory.Local

universe u s

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (ι : L →ₐ[K] D) {σ : L ≃ₐ[K] L} {j : Dˣ}
  (hconj : ∀ a : L, (j : D) * ι a = ι (σ a) * (j : D))
  (hdegree : Module.finrank K L = CentralSimple.reducedDegree K D)
  (horder : orderOf σ = CentralSimple.reducedDegree K D)

include hconj in
omit [FiniteDimensional K D] [Algebra.IsCentral K D] [FiniteDimensional K L] [IsGalois K L] in
private theorem normAdjusted_pow (t : L) (n : ℕ) :
    (ι t * (j : D)) ^ n = ι (CyclicNorm.coefficient σ t n) * (j : D) ^ n := by
  induction n with
  | zero => simp [CyclicNorm.coefficient]
  | succ n ih =>
    let c := CyclicNorm.coefficient σ t n
    calc
      (ι t * (j : D)) ^ (n + 1) = (ι t * (j : D)) * (ι c * (j : D) ^ n) := by
        rw [pow_succ', ih]
      _ = ι t * (((j : D) * ι c) * (j : D) ^ n) := by simp only [mul_assoc]
      _ = ι (t * σ c) * (j : D) ^ (n + 1) := by
        rw [hconj, map_mul, pow_succ']
        simp only [mul_assoc]
      _ = _ := by rw [CyclicNorm.coefficient_shift σ t n]

include hconj hdegree horder in
/-- Multiplying the implementing unit by an embedded coefficient multiplies
its central parameter by the norm of that coefficient. -/
theorem normAdjusted_pow_reducedDegree (t : L) :
    (ι t * (j : D)) ^ CentralSimple.reducedDegree K D =
      algebraMap K D (Algebra.norm K t) *
        algebraMap K D (cyclicParameter K D ι hconj hdegree horder : K) := by
  have hgen : ∀ τ, τ ∈ Subgroup.zpowers σ := by
    have htop : Subgroup.zpowers σ = ⊤ := by
      apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers σ)).mp
      rw [Nat.card_zpowers, horder, IsGalois.card_aut_eq_finrank, hdegree]
    rw [htop]
    exact fun τ => Subgroup.mem_top τ
  have hcoeff : CyclicNorm.coefficient σ t (CentralSimple.reducedDegree K D) =
      algebraMap K L (Algebra.norm K t) :=
    horder ▸ CyclicNorm.coefficient_order_eq_norm σ hgen t
  rw [normAdjusted_pow K D ι hconj, hcoeff, ι.commutes, algebraMap_cyclicParameter]

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
  (hcont : Continuous (algebraMap K L)) (he : localRamificationFactor K L = 1)
  (a : Kˣ)
  (horderDiff : (CentralSimple.reducedDegree K D : ℤ) ∣
    normalizedUnitOrder K (.ofMul a) -
      normalizedUnitOrder K (.ofMul (cyclicParameter K D ι hconj hdegree horder)))

include hcont he horderDiff in
private theorem exists_cyclicParameterAdjustment : ∃ t : Lˣ,
    normUnits K L t = a / cyclicParameter K D ι hconj hdegree horder := by
  apply (mem_normSubgroup_iff_of_localUnramified K L hcont he _).mpr
  simpa only [ofMul_div, map_sub, hdegree] using horderDiff

/-- Normalize the implementing unit to a prescribed central parameter when
the normalized orders agree modulo the unramified degree. -/
def normalizeImplementingUnit : Dˣ :=
  Units.map ι.toMonoidHom (exists_cyclicParameterAdjustment K D ι hconj hdegree horder
    hcont he a horderDiff).choose * j

/-- The norm-adjusted implementing unit has the prescribed central power. -/
theorem normalizeImplementingUnit_pow :
    (normalizeImplementingUnit K D ι hconj hdegree horder hcont he a horderDiff : D) ^
        CentralSimple.reducedDegree K D = algebraMap K D (a : K) := by
  let hn := exists_cyclicParameterAdjustment K D ι hconj hdegree horder hcont he a horderDiff
  let t := hn.choose
  have ht : Algebra.norm K (t : L) = ((a / cyclicParameter K D ι hconj hdegree horder : Kˣ) : K) :=
    congrArg Units.val hn.choose_spec
  change (ι (t : L) * (j : D)) ^ _ = _
  rw [normAdjusted_pow_reducedDegree K D ι hconj hdegree horder, ht, ← map_mul,
    ← Units.val_mul, div_mul_cancel]

/-- The norm adjustment preserves the original conjugation relation. -/
theorem normalizeImplementingUnit_mul (x : L) :
    (normalizeImplementingUnit K D ι hconj hdegree horder hcont he a horderDiff : D) * ι x =
      ι (σ x) * (normalizeImplementingUnit K D ι hconj hdegree horder hcont he a horderDiff : D) := by
  let t := (exists_cyclicParameterAdjustment K D ι hconj hdegree horder hcont he a horderDiff).choose
  change (ι (t : L) * (j : D)) * ι x = ι (σ x) * (ι (t : L) * (j : D))
  calc
    (ι (t : L) * (j : D)) * ι x = ι ((t : L) * σ x) * (j : D) := by
      rw [mul_assoc, hconj, ← mul_assoc, ← map_mul]
    _ = _ := by rw [mul_comm (t : L), map_mul, mul_assoc]

end Langlands.CentralDivision
