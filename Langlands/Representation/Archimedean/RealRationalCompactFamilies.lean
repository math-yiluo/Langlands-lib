import Langlands.Representation.Archimedean.RealSignedTailPolynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.Bilinear

/-! # Finite polynomial and rational families of compact operators -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealRationalCompactFamilies

open MvPolynomial RealBlockMultiplier RealSignedTailPolynomial

section PolynomialFamilies

variable {σ U V W : Type*}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Finite sums of scalar polynomial functions times constant vectors. -/
def polynomialFamilies (σ W : Type*) [AddCommGroup W] [Module ℂ W] :
    Submodule ℂ ((σ → ℂ) → W) :=
  Submodule.span ℂ (Set.range fun pv : MvPolynomial σ ℂ × W =>
    fun z => eval z pv.1 • pv.2)

theorem polynomial_vector (P : MvPolynomial σ ℂ) (v : W) :
    (fun z => eval z P • v) ∈ polynomialFamilies σ W :=
  Submodule.subset_span ⟨(P, v), rfl⟩

theorem polynomial_const (v : W) :
    (fun _ : σ → ℂ => v) ∈ polynomialFamilies σ W := by
  simpa using polynomial_vector (1 : MvPolynomial σ ℂ) v

theorem polynomial_bilinear (B : U →ₗ[ℂ] V →ₗ[ℂ] W)
    {F : (σ → ℂ) → U} {G : (σ → ℂ) → V}
    (hF : F ∈ polynomialFamilies σ U) (hG : G ∈ polynomialFamilies σ V) :
    (fun z => B (F z) (G z)) ∈ polynomialFamilies σ W := by
  apply Submodule.span_induction₂
    (p := fun f g _ _ => (fun z => B (f z) (g z)) ∈ polynomialFamilies σ W)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hF hG
  · rintro _ _ ⟨⟨P, v⟩, rfl⟩ ⟨⟨Q, w⟩, rfl⟩
    simpa [map_smul, smul_smul, mul_comm] using polynomial_vector (P * Q) (B v w)
  · intro G _
    convert polynomial_const (σ := σ) (0 : W) using 1
    funext z
    simp
  · intro F _
    convert polynomial_const (σ := σ) (0 : W) using 1
    funext z
    simp
  · intro F G H _ _ _ hF hG
    convert (polynomialFamilies σ W).add_mem hF hG using 1
    funext z
    simp
  · intro F G H _ _ _ hG hH
    convert (polynomialFamilies σ W).add_mem hG hH using 1
    funext z
    simp
  · intro c F G _ _ h
    convert (polynomialFamilies σ W).smul_mem c h using 1
    funext z
    simp
  · intro c F G _ _ h
    convert (polynomialFamilies σ W).smul_mem c h using 1
    funext z
    simp

theorem polynomial_scalar (P : MvPolynomial σ ℂ) :
    (fun z => eval z P) ∈ polynomialFamilies σ ℂ := by
  simpa using polynomial_vector P (1 : ℂ)

theorem polynomial_smul (P : MvPolynomial σ ℂ) {F : (σ → ℂ) → W}
    (hF : F ∈ polynomialFamilies σ W) :
    (fun z => eval z P • F z) ∈ polynomialFamilies σ W :=
  polynomial_bilinear (LinearMap.lsmul ℂ W) (polynomial_scalar P) hF

theorem polynomial_linear (L : U →ₗ[ℂ] W) {F : (σ → ℂ) → U}
    (hF : F ∈ polynomialFamilies σ U) :
    (fun z => L (F z)) ∈ polynomialFamilies σ W := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    rcases hF with ⟨⟨P, v⟩, rfl⟩
    simpa only [map_smul] using polynomial_vector P (L v)
  | zero =>
    convert polynomial_const (σ := σ) (0 : W) using 1
    funext z
    simp
  | add F G _ _ hF hG =>
    convert (polynomialFamilies σ W).add_mem hF hG using 1
    funext z
    simp
  | smul c F _ hF =>
    convert (polynomialFamilies σ W).smul_mem c hF using 1
    funext z
    simp

theorem scalar_polynomial {F : (σ → ℂ) → W}
    (hF : F ∈ polynomialFamilies σ W) (l : Module.Dual ℂ W) :
    ∃ P : MvPolynomial σ ℂ, ∀ z, l (F z) = eval z P := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    rcases hF with ⟨⟨P, v⟩, rfl⟩
    exact ⟨P * C (l v), fun z => by simp⟩
  | zero => exact ⟨0, fun z => by simp⟩
  | add F G _ _ hF hG =>
    obtain ⟨P, hP⟩ := hF
    obtain ⟨Q, hQ⟩ := hG
    exact ⟨P + Q, fun z => by simp [hP, hQ]⟩
  | smul c F _ hF =>
    obtain ⟨P, hP⟩ := hF
    exact ⟨C c * P, fun z => by simp [hP]⟩

/-- A vector polynomial vanishing on a product of infinite sets vanishes everywhere. -/
theorem polynomial_zero_of_grid {F : (σ → ℂ) → W}
    (hF : F ∈ polynomialFamilies σ W) (s : σ → Set ℂ)
    (hs : ∀ i, (s i).Infinite) (hgrid : ∀ z ∈ Set.pi Set.univ s, F z = 0) :
    ∀ z, F z = 0 := by
  intro z
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (F z)).mp
  intro l
  obtain ⟨P, hP⟩ := scalar_polynomial hF l
  have hP0 : P = 0 := MvPolynomial.funext_set s hs (fun x hx => by
    rw [← hP x, hgrid x hx, map_zero, map_zero])
  rw [hP z, hP0, map_zero]

theorem polynomial_eq_of_grid {F G : (σ → ℂ) → W}
    (hF : F ∈ polynomialFamilies σ W) (hG : G ∈ polynomialFamilies σ W)
    (s : σ → Set ℂ) (hs : ∀ i, (s i).Infinite)
    (hgrid : ∀ z ∈ Set.pi Set.univ s, F z = G z) :
    ∀ z, F z = G z := by
  have h := polynomial_zero_of_grid ((polynomialFamilies σ W).sub_mem hF hG) s hs
    (fun z hz => sub_eq_zero.mpr (hgrid z hz))
  exact fun z => sub_eq_zero.mp (h z)

end PolynomialFamilies

section RationalFamilies

variable {σ U V W : Type*}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- A polynomial vector family clearing the given denominator away from its zeros. -/
def HasDenominator (F : (σ → ℂ) → W) (D : MvPolynomial σ ℂ) : Prop :=
  ∃ A : (σ → ℂ) → W, A ∈ polynomialFamilies σ W ∧
    ∀ z, eval z D ≠ 0 → A z = eval z D • F z

theorem denominator_linear (L : U →ₗ[ℂ] W) {F : (σ → ℂ) → U}
    {D : MvPolynomial σ ℂ} (hF : HasDenominator F D) :
    HasDenominator (fun z => L (F z)) D := by
  obtain ⟨A, hA, hAF⟩ := hF
  refine ⟨fun z => L (A z), polynomial_linear L hA, fun z hz => ?_⟩
  change L (A z) = eval z D • L (F z)
  rw [hAF z hz, map_smul]

theorem denominator_bilinear (B : U →ₗ[ℂ] V →ₗ[ℂ] W)
    {F : (σ → ℂ) → U} {G : (σ → ℂ) → V} {D E : MvPolynomial σ ℂ}
    (hF : HasDenominator F D) (hG : HasDenominator G E) :
    HasDenominator (fun z => B (F z) (G z)) (D * E) := by
  obtain ⟨A, hA, hAF⟩ := hF
  obtain ⟨C, hC, hCG⟩ := hG
  refine ⟨fun z => B (A z) (C z), polynomial_bilinear B hA hC, fun z hz => ?_⟩
  change B (A z) (C z) = eval z (D * E) • B (F z) (G z)
  have hDE : eval z D * eval z E ≠ 0 := by simpa using hz
  rw [hAF z (mul_ne_zero_iff.mp hDE).1, hCG z (mul_ne_zero_iff.mp hDE).2]
  simp [map_smul, smul_smul, mul_comm]

/-- Equality on an infinite product grid extends wherever both denominators are nonzero. -/
theorem rational_eq_of_grid {F G : (σ → ℂ) → W} {D E : MvPolynomial σ ℂ}
    (hF : HasDenominator F D) (hG : HasDenominator G E)
    (s : σ → Set ℂ) (hs : ∀ i, (s i).Infinite)
    (hD : ∀ z ∈ Set.pi Set.univ s, eval z D ≠ 0)
    (hE : ∀ z ∈ Set.pi Set.univ s, eval z E ≠ 0)
    (hgrid : ∀ z ∈ Set.pi Set.univ s, F z = G z) :
    ∀ z, eval z D ≠ 0 → eval z E ≠ 0 → F z = G z := by
  obtain ⟨A, hA, hAF⟩ := hF
  obtain ⟨C, hC, hCG⟩ := hG
  have heq := polynomial_eq_of_grid (polynomial_smul E hA) (polynomial_smul D hC)
    s hs (fun z hz => by
      rw [hAF z (hD z hz), hCG z (hE z hz), hgrid z hz]
      simp [smul_smul, mul_comm])
  intro z hzD hzE
  have hh := heq z
  rw [hAF z hzD, hCG z hzE, smul_smul, smul_smul,
    mul_comm (eval z D) (eval z E)] at hh
  have hh' := congrArg (fun v => (eval z E * eval z D)⁻¹ • v) hh
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hzE hzD), one_smul] using hh'

end RationalFamilies

section OperatorFamilies

variable {σ W : Type*} [AddCommGroup W] [Module ℂ W]

theorem polynomial_mul {F G : (σ → ℂ) → Module.End ℂ W}
    (hF : F ∈ polynomialFamilies σ (Module.End ℂ W))
    (hG : G ∈ polynomialFamilies σ (Module.End ℂ W)) :
    (fun z => F z * G z) ∈ polynomialFamilies σ (Module.End ℂ W) :=
  polynomial_bilinear (LinearMap.mul ℂ (Module.End ℂ W)) hF hG

theorem denominator_mul {F G : (σ → ℂ) → Module.End ℂ W}
    {D E : MvPolynomial σ ℂ} (hF : HasDenominator F D) (hG : HasDenominator G E) :
    HasDenominator (fun z => F z * G z) (D * E) :=
  denominator_bilinear (LinearMap.mul ℂ (Module.End ℂ W)) hF hG

/-- Grid comparison may be restricted to any actual source set of compact vectors. -/
theorem rational_eq_on_of_grid {F G : (σ → ℂ) → Module.End ℂ W}
    {D E : MvPolynomial σ ℂ} (hF : HasDenominator F D) (hG : HasDenominator G E)
    (s : σ → Set ℂ) (hs : ∀ i, (s i).Infinite)
    (hD : ∀ z ∈ Set.pi Set.univ s, eval z D ≠ 0)
    (hE : ∀ z ∈ Set.pi Set.univ s, eval z E ≠ 0)
    (T : Set W) (hgrid : ∀ z ∈ Set.pi Set.univ s, ∀ v ∈ T, F z v = G z v) :
    ∀ z, eval z D ≠ 0 → eval z E ≠ 0 → ∀ v ∈ T, F z v = G z v := by
  intro z hzD hzE v hv
  let L : Module.End ℂ W →ₗ[ℂ] W :=
    { toFun := fun F => F v
      map_add' := fun F G => by simp
      map_smul' := fun c F => by simp }
  exact rational_eq_of_grid
    (denominator_linear L hF)
    (denominator_linear L hG)
    s hs hD hE (fun x hx => hgrid x hx v hv) z hzD hzE

end OperatorFamilies

section Denominators

variable {σ : Type*}

def denominator (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∏ i ∈ Finset.range B, (C ((ε : ℂ) + 2 * i + 1) + q)

def clearedSeq (ε : ℤ) (B m : ℕ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  (∏ i ∈ Finset.range m, (C ((ε : ℂ) + 2 * i + 1) - q)) *
    ∏ i ∈ Finset.Ico m B, (C ((ε : ℂ) + 2 * i + 1) + q)

def clearedMultiplier (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ) (j : ℤ) :
    MvPolynomial σ ℂ :=
  if 0 ≤ j then clearedSeq ε B (j.natAbs / 2) q
  else C ((-1 : ℂ) ^ ε.natAbs) * clearedSeq ε B (j.natAbs / 2) q

theorem eval_denominator (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ) (z : σ → ℂ) :
    eval z (denominator ε B q) =
      ∏ i ∈ Finset.range B, ((ε : ℂ) + 2 * i + 1 + eval z q) := by
  simp [denominator]

theorem clear_seq (ε : ℤ) {B m : ℕ} (hm : m ≤ B) (q : MvPolynomial σ ℂ)
    (z : σ → ℂ) (hden : eval z (denominator ε B q) ≠ 0) :
    eval z (denominator ε B q) * genericSeq (eval z q) ε m =
      eval z (clearedSeq ε B m q) := by
  have hsplit := Finset.prod_range_mul_prod_Ico
    (fun i => (ε : ℂ) + 2 * i + 1 + eval z q) hm
  have hm0 : (∏ i ∈ Finset.range m, ((ε : ℂ) + 2 * i + 1 + eval z q)) ≠ 0 := by
    intro hh
    rw [eval_denominator, ← hsplit, hh, zero_mul] at hden
    exact hden rfl
  rw [eval_denominator, ← hsplit, genericSeq, Finset.prod_div_distrib]
  simp only [clearedSeq, map_mul, map_prod, map_sub, eval_C, map_add]
  field_simp

theorem clear_multiplier (ε : ℤ) {B : ℕ} (q : MvPolynomial σ ℂ) (j : ℤ)
    (hj : j.natAbs / 2 ≤ B) (z : σ → ℂ)
    (hden : eval z (denominator ε B q) ≠ 0) :
    eval z (denominator ε B q) * genericMultiplier (eval z q) ε j =
      eval z (clearedMultiplier ε B q j) := by
  have hseq := clear_seq ε hj q z hden
  simp only [clearedMultiplier, genericMultiplier, extend]
  split_ifs
  · exact hseq
  · simp only [map_mul, eval_C]
    linear_combination ((-1 : ℂ) ^ ε.natAbs) * hseq

theorem denominator_ne_zero_of_re_pos {ε : ℤ} (hε : 0 ≤ ε) (B : ℕ)
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : 0 < (eval z q).re) :
    eval z (denominator ε B q) ≠ 0 := by
  rw [eval_denominator, Finset.prod_ne_zero_iff]
  intro i _
  exact genericSeq_denom_ne_zero hz hε i

/-- The positive arithmetic progression with the specified integral parity. -/
def positiveGrid (ε : ℤ) : Set ℂ :=
  Set.range fun n : ℕ => (ε : ℂ) + 2 * ((n : ℂ) + 1)

theorem positiveGrid_infinite (ε : ℤ) : (positiveGrid ε).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  have hh : (m : ℂ) = (n : ℂ) := by linear_combination h / 2
  exact Nat.cast_injective hh

end Denominators

section SpectralFamilies

variable {σ W : Type*} [AddCommGroup W] [Module ℂ W]

def clearedSpectral (π : ℤ → Module.End ℂ W) (S : Finset ℤ) (ε : ℤ) (B : ℕ)
    (q : MvPolynomial σ ℂ) (z : σ → ℂ) : Module.End ℂ W :=
  ∑ j ∈ S, eval z (clearedMultiplier ε B q j) • π j

theorem polynomial_clearedSpectral (π : ℤ → Module.End ℂ W) (S : Finset ℤ)
    (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ) :
    clearedSpectral π S ε B q ∈ polynomialFamilies σ (Module.End ℂ W) := by
  have hh := (polynomialFamilies σ (Module.End ℂ W)).sum_mem
    (fun j (_ : j ∈ S) => polynomial_vector (clearedMultiplier ε B q j) (π j))
  convert hh using 1
  funext z
  simp [clearedSpectral]

theorem clearedSpectral_eq (π : ℤ → Module.End ℂ W) (S : Finset ℤ)
    (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ)
    (hB : ∀ j ∈ S, j.natAbs / 2 ≤ B) (z : σ → ℂ)
    (hz : eval z (denominator ε B q) ≠ 0) :
    clearedSpectral π S ε B q z =
      eval z (denominator ε B q) • spectralMultiplier π S (genericMultiplier (eval z q) ε) := by
  symm
  change eval z (denominator ε B q) •
    spectralMultiplier π S (genericMultiplier (eval z q) ε) =
      ∑ j ∈ S, eval z (clearedMultiplier ε B q j) • π j
  rw [spectralMultiplier, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_smul, clear_multiplier ε q j (hB j hj) z hz]

theorem spectral_hasDenominator (π : ℤ → Module.End ℂ W) (S : Finset ℤ)
    (ε : ℤ) (B : ℕ) (q : MvPolynomial σ ℂ)
    (hB : ∀ j ∈ S, j.natAbs / 2 ≤ B) :
    HasDenominator (fun z => spectralMultiplier π S (genericMultiplier (eval z q) ε))
      (denominator ε B q) :=
  ⟨clearedSpectral π S ε B q, polynomial_clearedSpectral π S ε B q,
    clearedSpectral_eq π S ε B q hB⟩

theorem compact_generic_hasDenominator (N : ℕ) {p : ℕ} (hp : p + 1 < 3)
    (ε : ℤ) (q : MvPolynomial σ ℂ) :
    HasDenominator
      (fun z => spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
        (Finset.Icc (-(N : ℤ)) N) (genericMultiplier (eval z q) ε))
      (denominator ε N q) := by
  apply spectral_hasDenominator
  intro j hj
  have hb := Finset.mem_Icc.mp hj
  omega

end SpectralFamilies

section ThreeCrossings

abbrev Parameters := Fin 2 → ℂ
abbrev PV := MvPolynomial (Fin 2) ℂ
abbrev Compact (N : ℕ) := RealKTypeCount.degreeLE 3 N

def compactGeneric (N : ℕ) {p : ℕ} (hp : p + 1 < 3) (ε : ℤ) (q : PV)
    (z : Parameters) : Module.End ℂ (Compact N) :=
  spectralMultiplier (RealOrthogonalUncertainty.proj N hp)
    (Finset.Icc (-(N : ℤ)) N) (genericMultiplier (eval z q) ε)

def compactCleared (N : ℕ) {p : ℕ} (hp : p + 1 < 3) (ε : ℤ) (q : PV)
    (z : Parameters) : Module.End ℂ (Compact N) :=
  clearedSpectral (RealOrthogonalUncertainty.proj N hp) (Finset.Icc (-(N : ℤ)) N) ε N q z

theorem compactCleared_eq (N : ℕ) {p : ℕ} (hp : p + 1 < 3) (ε : ℤ) (q : PV)
    (z : Parameters) (hz : eval z (denominator ε N q) ≠ 0) :
    compactCleared N hp ε q z = eval z (denominator ε N q) • compactGeneric N hp ε q z := by
  apply clearedSpectral_eq _ _ _ _ _ _ z hz
  intro j hj
  have hb := Finset.mem_Icc.mp hj
  omega

def leftWord (N : ℕ) (ε η κ : ℤ) (z : Parameters) : Module.End ℂ (Compact N) :=
  compactGeneric N (p := 0) (by decide) η (X 1) z *
    compactGeneric N (p := 1) (by decide) κ (X 0 + X 1) z *
    compactGeneric N (p := 0) (by decide) ε (X 0) z

def rightWord (N : ℕ) (ε η κ : ℤ) (z : Parameters) : Module.End ℂ (Compact N) :=
  compactGeneric N (p := 1) (by decide) ε (X 0) z *
    compactGeneric N (p := 0) (by decide) κ (X 0 + X 1) z *
    compactGeneric N (p := 1) (by decide) η (X 1) z

def leftNumerator (N : ℕ) (ε η κ : ℤ) (z : Parameters) : Module.End ℂ (Compact N) :=
  compactCleared N (p := 0) (by decide) η (X 1) z *
    compactCleared N (p := 1) (by decide) κ (X 0 + X 1) z *
    compactCleared N (p := 0) (by decide) ε (X 0) z

def rightNumerator (N : ℕ) (ε η κ : ℤ) (z : Parameters) : Module.End ℂ (Compact N) :=
  compactCleared N (p := 1) (by decide) ε (X 0) z *
    compactCleared N (p := 0) (by decide) κ (X 0 + X 1) z *
    compactCleared N (p := 1) (by decide) η (X 1) z

def wordDenominator (N : ℕ) (ε η κ : ℤ) : PV :=
  denominator η N (X 1) * denominator κ N (X 0 + X 1) * denominator ε N (X 0)

theorem polynomial_leftNumerator (N : ℕ) (ε η κ : ℤ) :
    leftNumerator N ε η κ ∈ polynomialFamilies (Fin 2) (Module.End ℂ (Compact N)) := by
  unfold leftNumerator compactCleared
  apply polynomial_mul
  · apply polynomial_mul
    · exact polynomial_clearedSpectral _ _ _ _ _
    · exact polynomial_clearedSpectral _ _ _ _ _
  · exact polynomial_clearedSpectral _ _ _ _ _

theorem polynomial_rightNumerator (N : ℕ) (ε η κ : ℤ) :
    rightNumerator N ε η κ ∈ polynomialFamilies (Fin 2) (Module.End ℂ (Compact N)) := by
  unfold rightNumerator compactCleared
  apply polynomial_mul
  · apply polynomial_mul
    · exact polynomial_clearedSpectral _ _ _ _ _
    · exact polynomial_clearedSpectral _ _ _ _ _
  · exact polynomial_clearedSpectral _ _ _ _ _

theorem leftNumerator_eq (N : ℕ) (ε η κ : ℤ) (z : Parameters)
    (hz : eval z (wordDenominator N ε η κ) ≠ 0) :
    leftNumerator N ε η κ z = eval z (wordDenominator N ε η κ) • leftWord N ε η κ z := by
  have hd := hz
  simp only [wordDenominator, map_mul, mul_ne_zero_iff] at hd
  unfold leftNumerator leftWord
  rw [compactCleared_eq N _ η (X 1) z hd.1.1,
    compactCleared_eq N _ κ (X 0 + X 1) z hd.1.2,
    compactCleared_eq N _ ε (X 0) z hd.2]
  simp only [smul_mul_smul, wordDenominator, map_mul]

theorem rightNumerator_eq (N : ℕ) (ε η κ : ℤ) (z : Parameters)
    (hz : eval z (wordDenominator N ε η κ) ≠ 0) :
    rightNumerator N ε η κ z = eval z (wordDenominator N ε η κ) • rightWord N ε η κ z := by
  have hd := hz
  simp only [wordDenominator, map_mul, mul_ne_zero_iff] at hd
  unfold rightNumerator rightWord
  rw [compactCleared_eq N _ ε (X 0) z hd.2,
    compactCleared_eq N _ κ (X 0 + X 1) z hd.1.2,
    compactCleared_eq N _ η (X 1) z hd.1.1]
  simp only [smul_mul_smul, wordDenominator, map_mul]
  congr 1
  ring

theorem leftWord_hasDenominator (N : ℕ) (ε η κ : ℤ) :
    HasDenominator (leftWord N ε η κ) (wordDenominator N ε η κ) :=
  denominator_mul
    (denominator_mul (compact_generic_hasDenominator N (p := 0) (by decide) η (X 1))
      (compact_generic_hasDenominator N (p := 1) (by decide) κ (X 0 + X 1)))
    (compact_generic_hasDenominator N (p := 0) (by decide) ε (X 0))

theorem rightWord_hasDenominator (N : ℕ) (ε η κ : ℤ) :
    HasDenominator (rightWord N ε η κ) (wordDenominator N ε η κ) := by
  have hh := denominator_mul
    (denominator_mul (compact_generic_hasDenominator N (p := 1) (by decide) ε (X 0 : PV))
      (compact_generic_hasDenominator N (p := 0) (by decide) κ (X 0 + X 1)))
    (compact_generic_hasDenominator N (p := 1) (by decide) η (X 1))
  change HasDenominator (rightWord N ε η κ)
    (denominator ε N (X 0) * denominator κ N (X 0 + X 1) * denominator η N (X 1)) at hh
  have he : wordDenominator N ε η κ =
      denominator ε N (X 0) * denominator κ N (X 0 + X 1) * denominator η N (X 1) := by
    unfold wordDenominator
    ring
  rw [he]
  exact hh

def grid (ε η : ℤ) : Fin 2 → Set ℂ := ![positiveGrid ε, positiveGrid η]

theorem grid_infinite (ε η : ℤ) : ∀ i, (grid ε η i).Infinite := by
  intro i
  fin_cases i <;> exact positiveGrid_infinite _

theorem grid_re_pos {ε η : ℤ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    {z : Parameters} (hz : z ∈ Set.pi Set.univ (grid ε η)) :
    0 < (z 0).re ∧ 0 < (z 1).re := by
  have h0 : z 0 ∈ positiveGrid ε := hz 0 (Set.mem_univ _)
  have h1 : z 1 ∈ positiveGrid η := hz 1 (Set.mem_univ _)
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  rw [← ha, ← hb]
  have hεr : 0 ≤ (ε : ℝ) := by exact_mod_cast hε
  have hηr : 0 ≤ (η : ℝ) := by exact_mod_cast hη
  constructor <;> norm_num <;> positivity

theorem wordDenominator_ne_zero (N : ℕ) {ε η κ : ℤ}
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hκ : 0 ≤ κ) {z : Parameters}
    (hz0 : 0 < (z 0).re) (hz1 : 0 < (z 1).re) :
    eval z (wordDenominator N ε η κ) ≠ 0 := by
  simp only [wordDenominator, map_mul]
  exact mul_ne_zero
    (mul_ne_zero (denominator_ne_zero_of_re_pos hη N (X 1) z (by simpa using hz1))
      (denominator_ne_zero_of_re_pos hκ N (X 0 + X 1) z (by simpa using add_pos hz0 hz1)))
    (denominator_ne_zero_of_re_pos hε N (X 0) z (by simpa using hz0))

/-- The grid hypothesis is imposed only on the specified source vectors. -/
theorem threeCrossing_eq_of_grid (N : ℕ) {ε η κ : ℤ}
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hκ : 0 ≤ κ) (T : Set (Compact N))
    (hgrid : ∀ z ∈ Set.pi Set.univ (grid ε η), ∀ v ∈ T,
      leftWord N ε η κ z v = rightWord N ε η κ z v) :
    ∀ z, eval z (wordDenominator N ε η κ) ≠ 0 → ∀ v ∈ T,
      leftWord N ε η κ z v = rightWord N ε η κ z v := by
  have hden : ∀ z ∈ Set.pi Set.univ (grid ε η),
      eval z (wordDenominator N ε η κ) ≠ 0 := by
    intro z hz
    have hp := grid_re_pos hε hη hz
    exact wordDenominator_ne_zero N hε hη hκ hp.1 hp.2
  intro z hz
  exact rational_eq_on_of_grid (leftWord_hasDenominator N ε η κ)
    (rightWord_hasDenominator N ε η κ) (grid ε η) (grid_infinite ε η)
    hden hden T hgrid z hz hz

/-- The cleared identity extends even to zeros of the common denominator. -/
theorem threeCrossing_numerators_eq_of_grid (N : ℕ) {ε η κ : ℤ}
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hκ : 0 ≤ κ) (T : Set (Compact N))
    (hgrid : ∀ z ∈ Set.pi Set.univ (grid ε η), ∀ v ∈ T,
      leftWord N ε η κ z v = rightWord N ε η κ z v) :
    ∀ z, ∀ v ∈ T, leftNumerator N ε η κ z v = rightNumerator N ε η κ z v := by
  intro z v hv
  let L : Module.End ℂ (Compact N) →ₗ[ℂ] Compact N :=
    { toFun := fun F => F v
      map_add' := fun F G => by simp
      map_smul' := fun c F => by simp }
  apply polynomial_eq_of_grid
    (polynomial_linear L (polynomial_leftNumerator N ε η κ))
    (polynomial_linear L (polynomial_rightNumerator N ε η κ))
    (grid ε η) (grid_infinite ε η) ?_ z
  intro x hx
  have hp := grid_re_pos hε hη hx
  have hd := wordDenominator_ne_zero N hε hη hκ hp.1 hp.2
  change leftNumerator N ε η κ x v = rightNumerator N ε η κ x v
  rw [leftNumerator_eq N ε η κ x hd, rightNumerator_eq N ε η κ x hd]
  simp only [LinearMap.smul_apply, hgrid x hx v hv]

end ThreeCrossings

end Langlands.Archimedean.RealRationalCompactFamilies

namespace Langlands.Archimedean

open MvPolynomial RealRationalCompactFamilies

/-- Explicit finite generic crossing families extend from their positive parity grid. -/
def RealRationalCompactFamiliesStatement : Prop :=
  ∀ (N : ℕ) (ε η κ : ℤ), 0 ≤ ε → 0 ≤ η → 0 ≤ κ →
    ∀ (T : Set (Compact N)),
    (∀ z ∈ Set.pi Set.univ (grid ε η), ∀ v ∈ T,
      leftWord N ε η κ z v = rightWord N ε η κ z v) →
    (∀ z, ∀ v ∈ T, leftNumerator N ε η κ z v = rightNumerator N ε η κ z v) ∧
    (∀ z, eval z (wordDenominator N ε η κ) ≠ 0 → ∀ v ∈ T,
      leftWord N ε η κ z v = rightWord N ε η κ z v)

theorem realRationalCompactFamilies : RealRationalCompactFamiliesStatement :=
  fun N _ _ _ hε hη hκ T hgrid =>
    ⟨threeCrossing_numerators_eq_of_grid N hε hη hκ T hgrid,
      threeCrossing_eq_of_grid N hε hη hκ T hgrid⟩

end Langlands.Archimedean
