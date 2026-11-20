import Langlands.Automorphic.CuspidalL2.SiegelCover
import Langlands.Automorphic.GeneralLinearAdelicUniformForms
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth

/-! # Exponential torus growth from uniform moderate growth on `GL_n`

For a closed matrix embedding `rho` of `GL_n` and a finite plot-smooth function `φ` of uniform
moderate growth, every enveloping derivative of the transported matrix-side function grows at
most like `exp (c ∑ |x i|)` on the archimedean torus translates `torInf x * Q` of a compact set
`Q`, with one rate `c` for all derivatives. This is the growth hypothesis of the band bounds
in `SmoothWhittakerExpansion.Decay`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global Langlands.Automorphic Langlands.Automorphic.CuspidalL2
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]

local instance growthGeneralLinearIsAffine (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance growthFiniteSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FinitePlotSmoothRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))) :=
  Module.addCommMonoidToAddCommGroup ℂ

omit [NumberField F] in
/-- A continuous, nonnegative, submultiplicative function on the archimedean matrix group
grows at most exponentially in `∑ |x i|` along the archimedean torus. This is the argument of
`exists_matrixHeight_torInf_le` for an arbitrary such function. -/
theorem exists_torInf_le_of_submultiplicative {n : ℕ} (H : InfiniteAdelicGL F n → ℝ)
    (hH : Continuous H) (h0 : ∀ g, 0 ≤ H g) (hmul : ∀ g g', H (g * g') ≤ H g * H g') :
    ∃ C₀ c₀ : ℝ, 0 ≤ C₀ ∧ 0 ≤ c₀ ∧ ∀ x : Fin n → ℝ,
      H (torInf F n x) ≤ C₀ * Real.exp (c₀ * ∑ i, |x i|) := by
  have hpowle : ∀ (g : InfiniteAdelicGL F n) (k : ℕ), H (g ^ (k + 1)) ≤ H g ^ (k + 1) := by
    intro g k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ g (k + 1), pow_succ _ (k + 1)]
      exact (hmul _ _).trans (mul_le_mul_of_nonneg_right ih (h0 g))
  have hbox : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous fun y : Fin n → ℝ => H (torInf F n y) :=
    hH.comp (continuous_torInf F n)
  obtain ⟨M, hM⟩ := (hbox.image hcont).bddAbove
  set M₀ := max 1 M with hM₀
  have hM₀1 : 1 ≤ M₀ := le_max_left _ _
  have hM₀pos : 0 < M₀ := zero_lt_one.trans_le hM₀1
  refine ⟨M₀ ^ 2, Real.log M₀, by positivity, Real.log_nonneg hM₀1, fun x => ?_⟩
  set s := ∑ i, |x i| with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => abs_nonneg _
  set k := ⌈s⌉₊ + 1 with hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hks : s ≤ k := by
    rw [hk]; push_cast; linarith [Nat.le_ceil s]
  have hk2 : (k : ℝ) ≤ s + 2 := by
    rw [hk]; push_cast; linarith [Nat.ceil_lt_add_one hs0]
  set y : Fin n → ℝ := (k : ℝ)⁻¹ • x with hy
  have hxy : x = (k : ℝ) • y := by
    rw [hy, smul_smul, mul_inv_cancel₀ hkpos.ne', one_smul]
  have hybox : y ∈ Set.univ.pi fun _ : Fin n => Set.Icc (-1 : ℝ) 1 := by
    intro i _
    have hxi : |x i| ≤ s := Finset.single_le_sum (f := fun i => |x i|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have : |y i| ≤ 1 := by
      rw [hy, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, Nat.abs_cast,
        inv_mul_le_iff₀ hkpos, mul_one]
      exact hxi.trans hks
    exact abs_le.mp this
  have hHy : H (torInf F n y) ≤ M₀ := (hM ⟨y, hybox, rfl⟩).trans (le_max_right _ _)
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k = k' + 1 := ⟨⌈s⌉₊, rfl⟩
  have hpow : H (torInf F n x) ≤ M₀ ^ k := by
    rw [hxy, torInf_nsmul, hk']
    exact (hpowle _ k').trans (pow_le_pow_left₀ (h0 _) hHy _)
  refine hpow.trans ?_
  have hlog : 0 ≤ Real.log M₀ := Real.log_nonneg hM₀1
  calc M₀ ^ k = Real.exp (k * Real.log M₀) := by
        rw [Real.exp_nat_mul, Real.exp_log hM₀pos]
    _ ≤ Real.exp ((s + 2) * Real.log M₀) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hk2 hlog)
    _ = M₀ ^ 2 * Real.exp (Real.log M₀ * s) := by
        have h2 : Real.exp (2 * Real.log M₀) = M₀ ^ 2 := by
          rw [show (2 : ℝ) * Real.log M₀ = ((2 : ℕ) : ℝ) * Real.log M₀ by norm_num,
            Real.exp_nat_mul, Real.exp_log hM₀pos]
        rw [add_mul, Real.exp_add, h2, mul_comm s]
        exact mul_comm _ _

/-- A closed matrix embedding of `GL_{r+1}` has positive size: `GL_{r+1}(𝔸)` is nontrivial,
while `GL_0(𝔸)` is trivial. -/
theorem pos_of_isClosedSubgroup {r N : ℕ}
    (rho : GroupScheme.MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) (Fin N))
    (hrho : GroupScheme.IsClosedSubgroup rho) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    exfalso
    have hinj := (RepresentationGrowth.isClosedEmbedding_adelicMatrix F _ rho hrho).injective
    have hsub : Subsingleton (AdelicGL F 0) :=
      ⟨fun a b => Units.ext (Matrix.ext fun i _ => i.elim0)⟩
    let t : RationalGL F (r + 1) :=
      Units.map (Matrix.scalar (Fin (r + 1)) : F →+* Matrix (Fin (r + 1)) (Fin (r + 1)) F)
        (Units.mk0 (2 : F) two_ne_zero)
    have ht : t ≠ 1 := by
      intro htt
      have h1 := congrArg (fun a : RationalGL F (r + 1) =>
        (a : Matrix (Fin (r + 1)) (Fin (r + 1)) F) 0 0) htt
      simp [t] at h1
    let x := (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm
      (AdelicGL.rational F (r + 1) t)
    have hx : x = 1 := hinj (Subsingleton.elim _ _)
    apply ht
    apply AdelicGL.rational_injective F (r + 1)
    rw [map_one]
    have := congrArg (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)) hx
    simpa [x] using this
  · exact h

/-- **Exponential torus growth.** Under uniform moderate growth, every enveloping derivative
of the transported matrix-side function is bounded by `C * exp (c ∑ |x i|)` on
`torInf x * Q`, for compact `Q`, with one rate `c ≥ 0` for all derivatives. -/
theorem exists_torus_growth {n N d : ℕ} (hN : 0 < N)
    (rho : GroupScheme.MatrixRepresentation
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))
    (hsmooth : SmoothOfRelativeDimension d
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
    (hcalc : AdelicDifferentialCommutator F _ hsmooth)
    (φ : FinitePlotSmoothRationalFunctions F
      (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))
    (hφ : HasAdelicUniformModerateGrowth F _ rho hsmooth hcalc φ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (u : ArchimedeanGL.EnvelopingAlgebra F n) (Q : Set (AdelicGL F n)),
      IsCompact Q → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
        ‖ContinuousRationalFunctions.evaluate F n (finiteSmoothEnvelopingAction F n u
            (finitePlotSmoothGeneralLinearEquiv F n φ)).val
            (AdelicGL.ofInfinite F n (torInf F n x) * q)‖ ≤
          C * Real.exp (c * ∑ i, |x i|) := by
  obtain ⟨e, he⟩ := (hasAdelicUniformPolynomialGrowth_iff_generalLinear F n hsmooth hcalc rho
    φ).mp ((hasAdelicUniformModerateGrowth_iff F _ rho hsmooth hcalc hN φ).mp hφ)
  set ht : AdelicGL F n → ℝ := fun g => RepresentationGrowth.adelicHeight F _ rho
    ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm g) with hht
  have ht1 : ∀ g, 1 ≤ ht g := fun g => RepresentationGrowth.one_le_adelicHeight F _ rho hN _
  have htc : Continuous ht := (RepresentationGrowth.continuous_adelicHeight F _ rho hN).comp
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous
  have htmul : ∀ g g', ht (g * g') ≤ ht g * ht g' := by
    intro g g'
    simp only [hht, map_mul]
    exact RepresentationGrowth.adelicHeight_mul_le F _ rho hN _ _
  obtain ⟨C₀, c₀, hC₀, hc₀, hH⟩ := exists_torInf_le_of_submultiplicative
    (fun g => ht (AdelicGL.ofInfinite F n g)) (htc.comp (AdelicGL.ofInfinite F n).continuous)
    (fun g => zero_le_one.trans (ht1 _))
    (fun g g' => by simp only [map_mul]; exact htmul _ _)
  refine ⟨e * c₀, mul_nonneg (Nat.cast_nonneg e) hc₀, fun u Q hQ => ?_⟩
  obtain ⟨C, hC, hb⟩ := he u
  obtain ⟨M, hM⟩ := (hQ.image htc).bddAbove
  set M₁ := max 1 M with hM₁
  have hM₁0 : 0 ≤ M₁ := zero_le_one.trans (le_max_left _ _)
  refine ⟨C * (C₀ * M₁) ^ e, fun x q hq => ?_⟩
  have hq' : ht q ≤ M₁ := (hM ⟨q, hq, rfl⟩).trans (le_max_right _ _)
  have hprod : ht (AdelicGL.ofInfinite F n (torInf F n x) * q) ≤
      C₀ * Real.exp (c₀ * ∑ i, |x i|) * M₁ :=
    (htmul _ _).trans (mul_le_mul (hH x) hq' (zero_le_one.trans (ht1 _))
      (mul_nonneg hC₀ (Real.exp_pos _).le))
  calc _ ≤ C * ht (AdelicGL.ofInfinite F n (torInf F n x) * q) ^ e :=
        hb (AdelicGL.ofInfinite F n (torInf F n x) * q)
    _ ≤ C * (C₀ * Real.exp (c₀ * ∑ i, |x i|) * M₁) ^ e :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (ht1 _)) hprod e) hC
    _ = C * (C₀ * M₁) ^ e * Real.exp (e * c₀ * ∑ i, |x i|) := by
        rw [mul_assoc (e : ℝ), Real.exp_nat_mul]
        ring
