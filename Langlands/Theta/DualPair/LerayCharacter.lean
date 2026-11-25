import Langlands.Theta.DualPair.Unitary.Form
import Langlands.ClassFieldTheory.Local.QuadraticNormBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The splitting scalar

GKT §12.4.2 in Case `3₊`: the Leray character `χ_V = χ` ((12.5), p. 376) times the modulus of
Proposition 12.27 (1) (p. 372), with the condition (11.2) (p. 317) on the Leray splitting data.
For a quadratic extension `E / F` of nonarchimedean local fields, a character `χ` of `Eˣ` and
`m ∈ ℕ`, `splittingScalar F χ m z = χ(z) |N_{E/F} z|_F^{m/2}` (and `0` at `0`) is the scalar by
which the Levi part of the Siegel parabolic acts in the Leray splitting, through the determinant of
the upper left block (`β(m(a)) |det a|_E^{m/2}` with `β(m(a)) = χ(det a)`, Proposition 12.29,
p. 375). When `χ` restricted to `Fˣ` is the `m`-th power of the quadratic character of
`E / F`, it is multiplicative, of absolute value `|N z|^{m/2}`, satisfies
`splittingScalar (c z)⁻¹ |N z|^m = splittingScalar z`, equals `(η(t) |t|)^m` on `t ∈ Fˣ`, and is
`1` near `1` when `χ` is continuous (internal lemmas `sc_basic`, `sc_eventually_eq_one`). The
last uses the compact open subgroups `{z | v(N z) ≤ v(s)}` of `E`
(`LocalClassField.exists_addSubgroup_norm_mem_valuationBall`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis
open LocalClassField (valuationBall isCompact_valuationBall isOpen_valuationBall normSign
  normSign_mul exists_addSubgroup_norm_mem_valuationBall)

namespace Unitary.Internal

section Res

variable {R : Type*} [CommRing R] {E : Type*} [CommRing E] [Algebra R E]

open Classical in
/-- The restriction of `χ` to `Rˣ` is the `n`-th power of the quadratic character, written with the
subgroup of norms: `χ(a) = 1` on `K ⊔ N(Eˣ)` and `(-1)^n` off it. -/
def ResEtaPow (K : Subgroup Rˣ) (χ : Eˣ →* Circle) (n : ℕ) : Prop :=
  ∀ a : Rˣ, (χ (Units.map (algebraMap R E : R →* E) a) : ℂ) =
    if a ∈ K ⊔ (Units.map (Algebra.norm R : E →* R)).range then 1 else (-1) ^ n

theorem ResEtaPow.map_conj [Invertible (2 : R)] {c : E →ₐ[R] E} {ξ : E}
    (h : IsQuadraticInvolution c ξ) {K : Subgroup Rˣ} {χ : Eˣ →* Circle} {n : ℕ}
    (hχ : ResEtaPow K χ n) (z : Eˣ) : χ (Units.map (c : E →* E) z) = (χ z)⁻¹ := by
  refine h.map_map_eq_inv (fun z => ?_) z
  have h1 := hχ (Units.map (Algebra.norm R : E →* R) z)
  rw [ite_eq_left (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩))] at h1
  exact Circle.coe_eq_one.mp h1

end Res

end Unitary.Internal

open Unitary.Internal

section Sc

variable {E : Type} [Field E]

open Classical in
/-- The splitting scalar `z ↦ χ(z) |N_{E/F} z|_F^{m/2}`, `0` at `0`. -/
def splittingScalar (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Algebra F E] (χ : Eˣ →* Circle) (m : ℕ) (z : E) : ℂ :=
  if h : z = 0 then 0 else (χ (Units.mk0 z h) : ℂ) *
    ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z h)) ^
      ((m : ℝ) / 2) : ℝ) : ℂ)

end Sc

namespace Unitary.Internal



private theorem sc_units_eq_mul_nabs_norm_rpow {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : Eˣ) :
    splittingScalar F χ m (z : E) = (χ z : ℂ) *
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := by
  simp [splittingScalar, z.ne_zero]

private theorem rpow_natCast_div_two_sq {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x ^ ((m : ℝ) / 2)) ^ 2 = x ^ m := by
  rw [← Real.rpow_natCast (x ^ ((m : ℝ) / 2)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x m]
  congr 1
  push_cast
  ring

private theorem sc_zero' {E : Type} [Field E] (F : Type) [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) : splittingScalar F χ m 0 = 0 := by
  simp [splittingScalar]

theorem sc_basic : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (m : ℕ)
    (χ : Eˣ →* Circle) (_ : ResEtaPow (R := F) ⊥ χ m), splittingScalar F χ m 1 = 1 ∧ (∀ z z' : E,
    splittingScalar F χ m (z * z') = splittingScalar F χ m z * splittingScalar F χ m z') ∧
    (∀ z : Eˣ,
    splittingScalar F χ m (z : E) = (χ z : ℂ) * ((distribHaarChar F ((Units.map
    (Algebra.norm F : E →* F)) z) ^ ((m : ℝ) / 2) : ℝ) : ℂ)) ∧ (∀ z : Eˣ,
    ‖splittingScalar F χ m (z : E)‖ ^ 2 = distribHaarChar F ((Units.map
    (Algebra.norm F : E →* F)) z) ^ m) ∧ (∀ z : Eˣ,
    splittingScalar F χ m (c (z : E))⁻¹ * ((distribHaarChar F ((Units.map
    (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) = splittingScalar F χ m (z : E)) ∧ (∀ t : Fˣ,
    splittingScalar F χ m (algebraMap F E t) = (normSign E t * (distribHaarChar F t : ℝ)) ^ m) ∧
    ∀ z : Eˣ,
    splittingScalar F χ m ((z : E) * c (z : E)) = ((distribHaarChar F ((Units.map
    (Algebra.norm F : E →* F)) z) ^ m : ℝ) : ℂ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  have : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hinj := hE.algebraMap_injective
  have hinv : ∀ z, c (c z) = z := hE.involutive
  have hpos : ∀ t : Fˣ, (0 : ℝ) < distribHaarChar F t :=
    fun t => NNReal.coe_pos.mpr (distribHaarChar_pos (A := F) (g := t))
  have hmul : ∀ x y : Fˣ, ((distribHaarChar F (x * y) : NNReal) : ℝ) =
      (distribHaarChar F x : ℝ) * (distribHaarChar F y : ℝ) := fun x y => by
    rw [map_mul, NNReal.coe_mul]
  have hunit : ∀ z : Eˣ, splittingScalar F χ m (z : E) = (χ z : ℂ) *
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) := fun z => sc_units_eq_mul_nabs_norm_rpow F χ m z
  have hnorm : ∀ z : Eˣ, algebraMap F E ((Units.map (Algebra.norm F : E →* F) z : Fˣ) : F) =
      (z : E) * c z := fun z => by
    simpa using hE.algebraMap_norm (z : E)
  have hNc : ∀ z : Eˣ, Units.map (Algebra.norm F : E →* F) (Units.map (c : E →* E) z) =
      Units.map (Algebra.norm F : E →* F) z := by
    intro z
    apply Units.ext
    apply hinj
    rw [hnorm, hnorm]
    simp [hinv, mul_comm]
  have hNa : ∀ t : Fˣ, Units.map (Algebra.norm F : E →* F) (Units.map (algebraMap F E : F →* E) t)
      = t * t := by
    intro t
    apply Units.ext
    apply hinj
    rw [hnorm]
    simp
  have hbase : ∀ t : Fˣ, splittingScalar F χ m (algebraMap F E t) =
      (normSign E t * (distribHaarChar F t : ℝ)) ^ m := by
    intro t
    have h1 := hunit (Units.map (algebraMap F E : F →* E) t)
    simp only [Units.coe_map, MonoidHom.coe_ofClass] at h1
    rw [h1, hχ t, hNa, hmul, Real.mul_rpow (hpos t).le (hpos t).le, ← sq,
      rpow_natCast_div_two_sq (hpos t) m, mul_pow]
    simp only [normSign, bot_sup_eq]
    split_ifs with h₁ h₂ h₂ <;>
      first
        | (push_cast; ring1)
        | exact absurd (Subgroup.mem_sup_right h₂) h₁
        | exact absurd (by rwa [bot_sup_eq] at h₁) h₂
  refine ⟨?_, ?_, hunit, ?_, ?_, hbase, ?_⟩
  · simpa using hunit 1
  · intro z z'
    rcases eq_or_ne z 0 with rfl | hz
    · simp [sc_zero']
    rcases eq_or_ne z' 0 with rfl | hz'
    · simp [sc_zero']
    obtain ⟨u, rfl⟩ : ∃ u : Eˣ, (u : E) = z := ⟨Units.mk0 z hz, rfl⟩
    obtain ⟨u', rfl⟩ : ∃ u : Eˣ, (u : E) = z' := ⟨Units.mk0 z' hz', rfl⟩
    rw [← Units.val_mul, hunit, hunit, hunit]
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul]
    rw [Real.mul_rpow (hpos _).le (hpos _).le]
    push_cast
    ring
  · intro z
    rw [hunit, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (hpos _).le _), rpow_natCast_div_two_sq (hpos _) m]
  · intro z
    have h1 := hunit (Units.map (c : E →* E) z)⁻¹
    simp only [Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass, map_inv] at h1
    have hs := hpos (Units.map (Algebra.norm F : E →* F) z)
    have habs_inv : ∀ t : Fˣ, ((distribHaarChar F t⁻¹ : NNReal) : ℝ) =
        ((distribHaarChar F t : NNReal) : ℝ)⁻¹ := fun t => by
      rw [map_inv, NNReal.coe_inv]
    rw [h1, hNc, hunit,
      ResEtaPow.map_conj hE hχ z, inv_inv,
      NNReal.coe_inv, Real.inv_rpow hs.le, ← rpow_natCast_div_two_sq hs m]
    have ha0 : ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) z) ^
        ((m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos hs _).ne'
    push_cast at ha0 ⊢
    field_simp
  · intro z
    have hz : Units.map (Algebra.norm F : E →* F) z ∈ (Units.map (Algebra.norm F : E →* F)).range :=
      ⟨z, rfl⟩
    rw [← hnorm, hbase]
    simp [normSign, hz]


theorem sc_eventually_eq_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
        [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (m : ℕ) (χ : Eˣ →* Circle)
        (_ : Continuous χ),
    ∀ᶠ z in nhds (1 : E), splittingScalar F χ m z = 1 := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE m χ hχ
  have hfd : FiniteDimensional F E := hE.finite
  have htr : IsTopologicalRing E := hE.isTopologicalRing
  have hinv : ContinuousInv₀ E := hE.continuousInv₀
  have ht2 : T2Space E := hE.t2Space
  have hN : Continuous (Algebra.norm F : E → F) := hE.continuous_norm
  obtain ⟨L, hL, hLc, hLo⟩ := exists_addSubgroup_norm_mem_valuationBall hE 1

  have h0 : {t : Eˣ | ‖(χ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Eˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0

  have h1 : ∀ᶠ π in 𝓝 (0 : F), ∀ a ∈ (L : Set E), 1 + π • a ∈ U := by
    refine hLc.eventually_forall_of_forall_eventually fun a _ => ?_
    have : Tendsto (fun q : F × E => 1 + q.1 • q.2) (𝓝 (0, a)) (𝓝 1) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact this hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := exists_setOf_valuation_le_subset (inter_mem h1 h2)
  obtain ⟨hsU,
      hsv⟩ := hs (show (s : F) ∈ valuationBall s from show valuation F (s : F) ≤ valuation F
      (s : F) from le_rfl)
  set π : F := (s : F) with hπdef
  have hπ : π ≠ 0 := s.ne_zero

  have hmul : ∀ a ∈ (L : Set E), ∀ b ∈ (L : Set E), a * b ∈ (L : Set E) := by
    intro a ha b hb
    rw [hL] at ha hb ⊢
    show valuation F (Algebra.norm F (a * b)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [valuationBall] using ha
    have hb' : valuation F (Algebra.norm F b) ≤ 1 := by simpa [valuationBall] using hb
    rw [map_mul, map_mul]
    simpa using mul_le_one' ha' hb'
  have hsm : ∀ a ∈ (L : Set E), π • a ∈ (L : Set E) := by
    intro a ha
    rw [hL] at ha ⊢
    show valuation F (Algebra.norm F (π • a)) ≤ valuation F ((1 : Fˣ) : F)
    have ha' : valuation F (Algebra.norm F a) ≤ 1 := by simpa [valuationBall] using ha
    rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap, map_mul, map_pow]
    simpa using mul_le_one' (pow_le_one' hsv.le _) ha'

  set V : Set E := {z | π⁻¹ • (z - 1) ∈ (L : Set E)} with hVdef
  have hVo : IsOpen V := hLo.preimage (by fun_prop)
  have hV1 : (1 : E) ∈ V := by simp [V, L.zero_mem]
  have hVU : V ⊆ U := by
    intro z hz
    have := hsU _ hz
    rwa [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel] at this
  have hVpow : ∀ z ∈ V, ∀ n : ℕ, z ^ n ∈ V := by
    intro z hz n
    induction n with
    | zero => simpa using hV1
    | succ n ih =>
      show π⁻¹ • (z ^ (n + 1) - 1) ∈ (L : Set E)
      have hz' : z = 1 + π • (π⁻¹ • (z - 1)) := by
        rw [smul_smul, mul_inv_cancel₀ hπ, one_smul, add_sub_cancel]
      have e : π⁻¹ • (z ^ (n + 1) - 1) =
          π⁻¹ • (z ^ n - 1) + π • ((π⁻¹ • (z - 1)) * (π⁻¹ • (z ^ n - 1))) + π⁻¹ • (z - 1) := by
        have hp : algebraMap F E π ≠ 0 := (map_ne_zero _).mpr hπ
        simp only [Algebra.smul_def, map_inv₀]
        field_simp
        ring
      rw [e]
      exact L.add_mem (L.add_mem ih (hsm _ (hmul _ hz _ ih))) hz

  have h3 : Tendsto (fun z : E => Algebra.norm F z - 1) (𝓝 1) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [hVo.mem_nhds hV1, eventually_ne_nhds (one_ne_zero : (1 : E) ≠ 0),
      h3.eventually h2] with z hz hz0 hzN
  have hv : valuation F (Algebra.norm F z) = 1 := by
    simpa using (valuation F).map_one_add_of_lt hzN
  have hχz : χ (Units.mk0 z hz0) = 1 := by
    refine Circle.coe_eq_one.mp (Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt fun n => ?_)
    have : (Units.mk0 z hz0) ^ n ∈ Units.val ⁻¹' U := by simpa using hVU (hVpow z hz n)
    simpa using hUV this
  have hn : distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z hz0)) = 1 :=
    distribHaarChar_eq_one_of_valuation_eq_one (by simpa using hv)
  simp [splittingScalar, hz0, hχz, hn]


end Unitary.Internal

end Langlands.Theta
