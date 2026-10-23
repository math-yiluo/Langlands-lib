import Langlands.Representation.Shahidi.IntertwiningIntegral
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof

/-!
# Parabolic covariance of Shahidi's intertwining integral

If `f` transforms on the left under the standard `(m,n)` block parabolic by a
Levi scalar and a representation, the intertwining integral (0.1) of `f`
transforms under the `(n,m)` block parabolic, carried to total rank `m+n` by
`swapRank`, by the exchanged Levi data times the scaling factor of the change
of variables `a ↦ h₂⁻¹ a h₁`. Right invariance of `f` passes to the integral.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.Shahidi

open HarmonicAnalysis GeneralLinear SmoothWeakIntegral

universe uF uH uV

section Blocks

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (R : Type uF) [CommRing R]

/-- The exchange `(h₂, h₁) ↦ (h₁, h₂)` from the `(n,m)` Levi to the `(m,n)` Levi. -/
def twoBlockLeviSwap : (twoBlocks n m hn hm).Levi R ≃* (twoBlocks m n hm hn).Levi R :=
  ((twoBlockLeviEquiv hn hm R).trans MulEquiv.prodComm).trans
    (twoBlockLeviEquiv hm hn R).symm

@[simp] theorem twoBlockLeviSwap_first (l : (twoBlocks n m hn hm).Levi R) :
    twoBlockLeviSwap hm hn R l 0 = l 1 := rfl

@[simp] theorem twoBlockLeviSwap_second (l : (twoBlocks n m hn hm).Levi R) :
    twoBlockLeviSwap hm hn R l 1 = l 0 := rfl

/-- A matrix of the standard `(m,n)` radical is `u(a)`, with `a` its upper right block. -/
theorem eq_upper_of_mem_unipotentSubgroup {g : Langlands.GeneralLinear (m + n) R}
    (hg : g ∈ (twoBlocks m n hm hn).unipotentSubgroup R) :
    g = upper m n R (fun i j => g (i.castAdd n) (j.natAdd m)) := by
  rw [BlockShape.mem_unipotentSubgroup_iff] at hg
  obtain ⟨hp, hd⟩ := hg
  rw [twoBlocks_mem_parabolic_iff] at hp
  apply Units.ext
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rename_i a b
    apply Eq.trans ?_ (upper_first_first m n R _ a b).symm
    have h := hd 0 a b
    simp only [twoBlocks_index_first hm hn] at h
    exact h
  · rename_i a b
    exact (upper_first_second m n R (fun i j => g (i.castAdd n) (j.natAdd m)) a b).symm
  · rename_i a b
    exact (hp a b).trans (upper_second_first m n R _ a b).symm
  · rename_i a b
    apply Eq.trans ?_ (upper_second_second m n R _ a b).symm
    have h := hd 1 a b
    simp only [twoBlocks_index_second hm hn] at h
    exact h

/-- Every element of the standard `(m,n)` parabolic is `u(a) diag(g₀, g₁)`, where
`(g₀, g₁)` is its Levi projection. -/
theorem exists_upper_mul_blockSum (p : (twoBlocks m n hm hn).parabolic R) :
    ∃ a : Matrix (Fin m) (Fin n) R,
      (p : Langlands.GeneralLinear (m + n) R) =
        upper m n R a * blockSum (n := m) (m := n)
          ((twoBlocks m n hm hn).leviProjection R p 0,
            (twoBlocks m n hm hn).leviProjection R p 1) := by
  let B := twoBlocks m n hm hn
  let u := B.unipotentPart R p
  have hu : ((u : B.parabolic R) : Langlands.GeneralLinear (m + n) R) ∈ B.unipotentSubgroup R :=
    ⟨u, u.property, rfl⟩
  have hp : (u : B.parabolic R) * B.leviInParabolic R (B.leviProjection R p) = p :=
    (B.decomposition R).left_inv p
  refine ⟨fun i j => ((u : B.parabolic R) : Langlands.GeneralLinear (m + n) R)
    (i.castAdd n) (j.natAdd m), ?_⟩
  rw [← eq_upper_of_mem_unipotentSubgroup hm hn R hu]
  refine Eq.trans ?_ (congrArg
    (fun z => ((u : B.parabolic R) : Langlands.GeneralLinear (m + n) R) * z)
    (twoBlocks_leviEmbedding hm hn R (B.leviProjection R p)))
  conv_lhs => rw [← hp]
  rfl

end Blocks

section Measurable

variable {F : Type uF} [Field F] [MeasurableSpace F] [MeasurableAdd₂ F] [MeasurableMul F]

theorem measurable_mul_mul {k r s l : ℕ} (A : Matrix (Fin k) (Fin r) F)
    (B : Matrix (Fin s) (Fin l) F) :
    Measurable (fun a : Matrix (Fin r) (Fin s) F => A * a * B) := by
  refine Matrix.measurable_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply]
  refine Finset.measurable_sum _ fun x _ => Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun y _ => Matrix.measurable_apply.const_mul _

variable {m n : ℕ}

/-- The change of variables `a ↦ h₂⁻¹ a h₁` of the coordinates of `U'`. -/
def rectangularConj (h₂ : Langlands.GeneralLinear n F) (h₁ : Langlands.GeneralLinear m F) :
    Matrix (Fin n) (Fin m) F ≃ᵐ Matrix (Fin n) (Fin m) F where
  toFun a := ((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) * a *
    (h₁ : Matrix (Fin m) (Fin m) F)
  invFun a := (h₂ : Matrix (Fin n) (Fin n) F) * a *
    ((h₁⁻¹ : Langlands.GeneralLinear m F) : Matrix (Fin m) (Fin m) F)
  left_inv a := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  right_inv a := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  measurable_toFun := measurable_mul_mul _ _
  measurable_invFun := measurable_mul_mul _ _

@[simp] theorem rectangularConj_apply (h₂ : Langlands.GeneralLinear n F)
    (h₁ : Langlands.GeneralLinear m F) (a : Matrix (Fin n) (Fin m) F) :
    rectangularConj h₂ h₁ a = ((h₂⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) *
      a * (h₁ : Matrix (Fin m) (Fin m) F) := rfl

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
variable [MeasurableSpace F.Carrier] [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]

/-- Over a `p`-adic field, `a ↦ h₂⁻¹ a h₁` scales every Borel additive Haar measure
on `n × m` matrices by `|det h₂|^m |det h₁|^(-n)`. -/
theorem map_rectangularConj_padic :
    letI := T.topology
    ∀ [BorelSpace (Matrix (Fin n) (Fin m) F.Carrier)]
      (μ : Measure (Matrix (Fin n) (Fin m) F.Carrier)) [μ.IsAddHaarMeasure]
      (h₂ : Langlands.GeneralLinear n F.Carrier) (h₁ : Langlands.GeneralLinear m F.Carrier),
      μ.map (rectangularConj h₂ h₁) =
        ((T.determinantNorm n h₂ : ℝ≥0) ^ m / (T.determinantNorm m h₁ : ℝ≥0) ^ n) • μ := by
  let := T.topology
  intro _ μ _ h₂ h₁
  have h := padicRectangularHaarScaling F T n m μ h₂⁻¹ h₁⁻¹
  rw [inv_inv] at h
  change μ.map (fun a => ((h₂⁻¹ : Langlands.GeneralLinear n F.Carrier) :
    Matrix (Fin n) (Fin n) F.Carrier) * a * (h₁ : Matrix (Fin m) (Fin m) F.Carrier)) = _
  rw [h]
  congr 1
  simp only [map_inv, Units.val_inv_eq_inv_val, inv_pow, div_eq_mul_inv, inv_inv, mul_inv]

end Padic

end Measurable

section Covariance

variable {F : Type uF} [Field F] [MeasurableSpace F]
variable {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
variable {ρ : Representation ℂ H V} {μ : Measure (Matrix (Fin n) (Fin m) F)}

omit [IsTopologicalGroup H] in
/-- Translation of the coordinates does not change a weak integral against a
translation-invariant measure. -/
theorem hasIntegral_add_right [MeasurableAdd F] [μ.IsAddLeftInvariant]
    {Φ : Matrix (Fin n) (Fin m) F → V} {v : V} (h : HasIntegral ρ μ Φ v)
    (b : Matrix (Fin n) (Fin m) F) :
    HasIntegral ρ μ (fun a => Φ (a + b)) v := by
  have hmeas (c : Matrix (Fin n) (Fin m) F) :
      Measurable (fun a : Matrix (Fin n) (Fin m) F => a + c) :=
    Matrix.measurable_iff.2 fun i j => Matrix.measurable_apply.add_const (c i j)
  let e : Matrix (Fin n) (Fin m) F ≃ᵐ Matrix (Fin n) (Fin m) F :=
    { toFun := fun a => a + b
      invFun := fun a => a + -b
      left_inv := fun a => add_neg_cancel_right a b
      right_inv := fun a => neg_add_cancel_right a b
      measurable_toFun := hmeas b
      measurable_invFun := hmeas (-b) }
  have he : μ.map e = (1 : ℝ≥0) • μ := by
    rw [one_smul]
    change μ.map (fun a => a + b) = μ
    simp_rw [add_comm _ b]
    exact map_add_left_eq_self μ b
  have h' := h.comp_measurableEquiv e 1 he
  rw [show ((1 : ℝ≥0) : ℂ) = 1 by simp, one_smul] at h'
  exact h'

/-- Parabolic covariance of (0.1). Suppose `f(p x) = χ(m_p) • ρ(τ(m_p)) f(x)` for
every `p` in the standard `(m,n)` parabolic with Levi projection `m_p`, and the
change of variables `a ↦ h₂⁻¹ a h₁` multiplies `μ` by `c(h₂,h₁)`. Then for `p`
in the `(n,m)` parabolic with Levi projection `l = (h₂, h₁)`, the integral at
`p x` (in total rank `m+n`) is `χ(h₁,h₂) c(l) ρ(τ(h₁,h₂))` applied to the
integral at `x`. -/
theorem HasIntertwiningIntegral.parabolic [MeasurableAdd₂ F] [MeasurableMul F]
    [μ.IsAddLeftInvariant]
    {f A : Langlands.GeneralLinear (m + n) F → V} (hA : HasIntertwiningIntegral m n ρ μ f A)
    (χ : (twoBlocks m n hm hn).Levi F → ℂ) (τ : (twoBlocks m n hm hn).Levi F → H)
    (hf : ∀ (p : (twoBlocks m n hm hn).parabolic F) (x : Langlands.GeneralLinear (m + n) F),
      f (p * x) = χ ((twoBlocks m n hm hn).leviProjection F p) •
        ρ (τ ((twoBlocks m n hm hn).leviProjection F p)) (f x))
    (c : (twoBlocks n m hn hm).Levi F → ℝ≥0)
    (hμ : ∀ l, μ.map (rectangularConj (l 0) (l 1)) = c l • μ)
    (p : (twoBlocks n m hn hm).parabolic F) (x : Langlands.GeneralLinear (m + n) F) :
    HasIntegral ρ μ (intertwiningIntegrand m n (swapRank m n F p * x) f)
      ((χ (twoBlockLeviSwap hm hn F ((twoBlocks n m hn hm).leviProjection F p)) *
          c ((twoBlocks n m hn hm).leviProjection F p)) •
        ρ (τ (twoBlockLeviSwap hm hn F ((twoBlocks n m hn hm).leviProjection F p))) (A x)) := by
  obtain ⟨a, ha⟩ := exists_upper_mul_blockSum hn hm F p
  set l := (twoBlocks n m hn hm).leviProjection F p
  have hsw : swapRank m n F p * x =
      intertwiningUnipotent m n F a * (swapRank m n F
        (blockSum (n := n) (m := m) (l 0, l 1)) * x) := by
    rw [ha, map_mul, mul_assoc]
    rfl
  rw [hsw, intertwiningIntegrand_unipotent_mul]
  refine hasIntegral_add_right
    (Φ := intertwiningIntegrand m n (swapRank m n F
      (blockSum (n := n) (m := m) (l 0, l 1)) * x) f)
    ?_ a
  have hf' : ∀ y, f (blockSum (n := m) (m := n) (l 1, l 0) * y) =
      χ (twoBlockLeviSwap hm hn F l) • ρ (τ (twoBlockLeviSwap hm hn F l)) (f y) := by
    intro y
    have h := hf ((twoBlocks m n hm hn).leviInParabolic F (twoBlockLeviSwap hm hn F l)) y
    rw [BlockShape.leviProjection_section, BlockShape.leviInParabolic_val,
      twoBlocks_leviEmbedding] at h
    exact h
  exact hA.levi (l 1) (l 0) _ _ hf' (rectangularConj (l 0) (l 1)) (fun _ => rfl) (c l) (hμ l) x

section Operator

variable (hcofinal : ∀ K : OpenSubgroup H, ∃ L : OpenSubgroup H,
  IsCompact (L : Set H) ∧ L ≤ K) (hρ : IsSmooth ρ)

/-- The operator values transform under the `(n,m)` parabolic as in
`HasIntertwiningIntegral.parabolic`. -/
theorem intertwiningOperator_parabolic [MeasurableAdd₂ F] [MeasurableMul F]
    [μ.IsAddLeftInvariant] (f : intertwiningDomain m n ρ μ)
    (χ : (twoBlocks m n hm hn).Levi F → ℂ) (τ : (twoBlocks m n hm hn).Levi F → H)
    (hf : ∀ (p : (twoBlocks m n hm hn).parabolic F) (x : Langlands.GeneralLinear (m + n) F),
      f.val (p * x) = χ ((twoBlocks m n hm hn).leviProjection F p) •
        ρ (τ ((twoBlocks m n hm hn).leviProjection F p)) (f.val x))
    (c : (twoBlocks n m hn hm).Levi F → ℝ≥0)
    (hμ : ∀ l, μ.map (rectangularConj (l 0) (l 1)) = c l • μ)
    (p : (twoBlocks n m hn hm).parabolic F) (x : Langlands.GeneralLinear (m + n) F) :
    intertwiningOperator m n ρ μ hcofinal hρ f (swapRank m n F p * x) =
      (χ (twoBlockLeviSwap hm hn F ((twoBlocks n m hn hm).leviProjection F p)) *
          c ((twoBlocks n m hn hm).leviProjection F p)) •
        ρ (τ (twoBlockLeviSwap hm hn F ((twoBlocks n m hn hm).leviProjection F p)))
          (intertwiningOperator m n ρ μ hcofinal hρ f x) :=
  (hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f _).unique hcofinal hρ
    ((hasIntertwiningIntegral_intertwiningOperator hcofinal hρ f).parabolic hm hn χ τ hf c hμ p x)

/-- Right invariance of `f` under `k` passes to the operator values. -/
theorem intertwiningOperator_mul_right (f : intertwiningDomain m n ρ μ)
    (k : Langlands.GeneralLinear (m + n) F) (hk : ∀ x, f.val (x * k) = f.val x)
    (x : Langlands.GeneralLinear (m + n) F) :
    intertwiningOperator m n ρ μ hcofinal hρ f (x * k) =
      intertwiningOperator m n ρ μ hcofinal hρ f x := by
  have h := intertwiningOperator_rightTranslate hcofinal hρ f k
  have he : (⟨fun x => f.val (x * k), rightTranslate_mem_intertwiningDomain f.property k⟩ :
      intertwiningDomain m n ρ μ) = f := Subtype.ext (funext hk)
  rw [he] at h
  exact (congrFun h x).symm

end Operator

end Covariance

end Langlands.Shahidi
