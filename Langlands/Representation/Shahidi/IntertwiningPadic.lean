import Langlands.Representation.Shahidi.IntertwiningInduced

/-!
# Shahidi's intertwining operator over a p-adic field

The operator `A(s, π, w_{m,n})` of (0.1) from the p-adic `I(s, π₁ ⊗ π₂)` of
`Langlands.Representation.Shahidi.Induction` to the p-adic `I(-s, π₂ ⊗ π₁)`, on its
convergence domain: compact open cofinality of the Levi, the covariance laws for the
normalized absolute value, and the Jacobian law for additive Haar measures.
-/

noncomputable section

open scoped NNReal

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi GeneralLinear MeasureTheory HarmonicAnalysis SmoothWeakIntegral

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem shahidiTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- Every open subgroup of a block Levi contains a compact open subgroup. -/
theorem leviCompactOpenCofinal {r : ℕ} (B : BlockShape r) :
    letI := T.leviTopology B
    CompactOpenCofinal (B.Levi F.Carrier) := by
  let := T.leviTopology B
  intro K
  obtain ⟨L, hL, hLK⟩ := T.leviCompactOpen B K (K.isOpen.mem_nhds K.one_mem)
  exact ⟨L, hL, fun x hx => hLK hx⟩

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (s : ℂ)
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear m F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear n F.Carrier) V₂)

/-- The inducing representation of the p-adic `I(s, π₁ ⊗ π₂)` on the `(m,n)` parabolic. -/
abbrev shahidiSourceInducing :
    Representation ℂ ((twoBlocks m n hm hn).parabolic F.Carrier)
      (PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  twist (T.parabolicHalfModulus (twoBlocks m n hm hn))
    (((twoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair s π₁ π₂)).comp
      ((twoBlocks m n hm hn).leviProjection F.Carrier))

/-- The inducing representation of the p-adic `I(-s, π₂ ⊗ π₁)` on the parabolic of
`swappedTwoBlocks m n`. -/
abbrev shahidiTargetInducing :
    Representation ℂ ((swappedTwoBlocks m n hm hn).parabolic F.Carrier)
      (PiTensorProduct ℂ (pairCarrier V₂ V₁)) :=
  twist (T.parabolicHalfModulus (swappedTwoBlocks m n hm hn))
    (((swappedTwoBlocks m n hm hn).blockTensor (T.shahidiTwistedPair (-s) π₂ π₁)).comp
      ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier))

/-- The p-adic `I(s, π₁ ⊗ π₂)` satisfies the source covariance law for the normalized
absolute value. -/
theorem isSourceCovariance_shahidiSource :
    IsSourceCovariance hm hn π₁ π₂ T.shahidiAbsoluteValue s
      (T.shahidiSourceInducing hm hn s π₁ π₂) := by
  intro g v
  change ((NNReal.sqrt (T.leviModulus (twoBlocks m n hm hn)
      ((twoBlocks m n hm hn).leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
    (twoBlocks m n hm hn).blockTensor
      (pairFamily (twist (T.determinantComplexPower m (s / 2)) π₁)
        (twist (T.determinantComplexPower n (-(s / 2))) π₂))
      ((twoBlocks m n hm hn).leviProjection F.Carrier g) v = _
  rw [blockTensor_pairFamily_twist, LinearMap.smul_apply, smul_smul]
  congr 1
  rw [T.leviModulus_twoBlocks]
  erw [T.determinantComplexPower_apply, T.determinantComplexPower_apply]
  refine (sqrt_mul_cpow_mul_cpow
    (T.determinantNorm m ((twoBlocks m n hm hn).leviProjection F.Carrier g 0))
    (T.determinantNorm n ((twoBlocks m n hm hn).leviProjection F.Carrier g 1)) m n
    (s / 2) (-(s / 2))).trans ?_
  rw [show s / 2 + (n : ℂ) / 2 = (s + n) / 2 by ring,
    show -(s / 2) - (m : ℂ) / 2 = -((s + m) / 2) by ring]
  rfl

/-- The p-adic `I(-s, π₂ ⊗ π₁)` satisfies the target covariance law for the normalized
absolute value. -/
theorem isTargetCovariance_shahidiTarget :
    IsTargetCovariance hm hn π₁ π₂ T.shahidiAbsoluteValue s
      (T.shahidiTargetInducing hm hn s π₁ π₂) := by
  intro g v
  change ((NNReal.sqrt (T.leviModulus (swappedTwoBlocks m n hm hn)
      ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier
        (swappedParabolicEquiv hm hn F.Carrier g)) : ℝ≥0) : ℝ) : ℂ) •
    (twoBlocks n m hn hm).blockTensor
      (pairFamily (twist (T.determinantComplexPower n (-s / 2)) π₂)
        (twist (T.determinantComplexPower m (-(-s / 2))) π₁))
      ((swappedTwoBlocks m n hm hn).leviProjection F.Carrier
        (swappedParabolicEquiv hm hn F.Carrier g)) v = _
  rw [leviProjection_swappedParabolicEquiv, blockTensor_pairFamily_twist, LinearMap.smul_apply,
    smul_smul]
  congr 1
  rw [T.leviModulus_swappedTwoBlocks]
  erw [T.determinantComplexPower_apply, T.determinantComplexPower_apply]
  refine (sqrt_mul_cpow_mul_cpow
    (T.determinantNorm n ((twoBlocks n m hn hm).leviProjection F.Carrier g 0))
    (T.determinantNorm m ((twoBlocks n m hn hm).leviProjection F.Carrier g 1)) n m
    (-s / 2) (-(-s / 2))).trans ?_
  rw [show -s / 2 + (m : ℂ) / 2 = (m - s) / 2 by ring,
    show -(-s / 2) - (n : ℂ) / 2 = (s - n) / 2 by ring]
  rfl

section Measure

variable [MeasurableSpace F.Carrier] [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]

/-- Every Borel additive Haar measure on the `n × m` matrices satisfies the Jacobian law
of the intertwining integral for the normalized absolute value. -/
theorem isModulusScaling_padic :
    letI := T.topology
    ∀ [BorelSpace (Matrix (Fin n) (Fin m) F.Carrier)]
      (μ : Measure (Matrix (Fin n) (Fin m) F.Carrier)) [μ.IsAddHaarMeasure],
      IsModulusScaling hm hn T.shahidiAbsoluteValue μ := by
  let := T.topology
  intro _ μ _ l
  refine (map_rectangularConj_padic F T μ (l 0) (l 1)).trans ?_
  rw [Langlands.Shahidi.leviModulus_twoBlocks,
    determinantAbs_eq_determinantNorm (abv := T.shahidiAbsoluteValue) (fun _ => rfl),
    determinantAbs_eq_determinantNorm (abv := T.shahidiAbsoluteValue) (fun _ => rfl)]
  congr 1
  simp only [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]

variable (μ : Measure (Matrix (Fin n) (Fin m) F.Carrier))

/-- The convergence domain of (0.1) in the p-adic `I(s, π₁ ⊗ π₂)`: the `f` for which
`∫_{U'} f(w_{m,n} u' g) du'` exists as a weak integral at every `g`. -/
abbrev shahidiSourceDomain : Submodule ℂ (T.ShahidiSourceSpace hm hn s π₁ π₂) :=
  letI := T.topology
  letI := T.shahidiTopologicalRing
  convergenceDomain hm hn π₁ π₂ μ (T.shahidiSourceInducing hm hn s π₁ π₂)

omit [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier] in
/-- The convergence domain is a subrepresentation of the p-adic `I(s, π₁ ⊗ π₂)`. -/
theorem shahidiSource_mem_shahidiSourceDomain {f : T.ShahidiSourceSpace hm hn s π₁ π₂}
    (hf : f ∈ T.shahidiSourceDomain hm hn s π₁ π₂ μ) (g : GeneralLinear (m + n) F.Carrier) :
    T.shahidiSource hm hn s π₁ π₂ g f ∈ T.shahidiSourceDomain hm hn s π₁ π₂ μ := by
  let := T.topology
  let := T.shahidiTopologicalRing
  exact smoothInduced_mem_convergenceDomain hm hn π₁ π₂ μ hf g

variable [μ.IsAddLeftInvariant] {μ}

/-- Shahidi's intertwining operator `A(s, π, w_{m,n})` of (0.1) over a p-adic field, from
the convergence domain in `I(s, π₁ ⊗ π₂)` to `I(-s, π₂ ⊗ π₁)`:
`A f(g) = ∫_{U'} f(w_{m,n} u' g) du'`, with values carried from `V₁ ⊗ V₂` to `V₂ ⊗ V₁`. -/
def shahidiIntertwining (hμ : IsModulusScaling hm hn T.shahidiAbsoluteValue μ) :
    letI := T.topology
    IsSmooth π₁ → IsSmooth π₂ →
      T.shahidiSourceDomain hm hn s π₁ π₂ μ →ₗ[ℂ] T.ShahidiTargetSpace hm hn s π₁ π₂ :=
  letI := T.topology
  letI := T.shahidiTopologicalRing
  letI := T.leviTopologicalGroup (twoBlocks m n hm hn)
  fun hπ₁ hπ₂ => swappedOperator hm hn (T.leviCompactOpenCofinal (twoBlocks m n hm hn)) hπ₁ hπ₂
    (T.isSourceCovariance_shahidiSource hm hn s π₁ π₂)
    (T.isTargetCovariance_shahidiTarget hm hn s π₁ π₂) hμ

variable (hμ : IsModulusScaling hm hn T.shahidiAbsoluteValue μ)
  {π₁ π₂}

/-- The value of `A f` at `g` is the flip of the function-level integral at `g`. -/
theorem shahidiTargetEval_shahidiIntertwining :
    letI := T.topology
    letI := T.leviTopologicalGroup (twoBlocks m n hm hn)
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (f : T.shahidiSourceDomain hm hn s π₁ π₂ μ)
      (g : GeneralLinear (m + n) F.Carrier),
      T.shahidiTargetEval hm hn s π₁ π₂ (T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂ f) g =
        pairFlip (intertwiningOperator m n (pairRepresentation hm hn π₁ π₂) μ
          (T.leviCompactOpenCofinal (twoBlocks m n hm hn))
          (isSmooth_pairRepresentation hm hn hπ₁ hπ₂)
          ⟨T.shahidiSourceEval hm hn s π₁ π₂ f.val, f.property⟩ g) := by
  let := T.topology
  intro _ _ _ _
  rfl

/-- `A f(g)` is the flip of the weak integral `∫_{U'} f(w_{m,n} u' g) du'`. -/
theorem hasIntegral_shahidiIntertwining :
    letI := T.topology
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (f : T.shahidiSourceDomain hm hn s π₁ π₂ μ)
      (g : GeneralLinear (m + n) F.Carrier),
      HasIntegral (pairRepresentation hm hn π₁ π₂) μ
        (fun a => T.shahidiSourceEval hm hn s π₁ π₂ f.val
          (blockWeyl m n F.Carrier * intertwiningUnipotent m n F.Carrier a * g))
        (pairFlip.symm (T.shahidiTargetEval hm hn s π₁ π₂
          (T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂ f) g)) := by
  let := T.topology
  let := T.shahidiTopologicalRing
  let := T.leviTopologicalGroup (twoBlocks m n hm hn)
  intro hπ₁ hπ₂ f g
  exact hasIntegral_swappedOperator hm hn _ hπ₁ hπ₂ _ _ hμ f g

/-- Every smooth functional `ℓ` of `π₁ ⊗ π₂` satisfies
`ℓ(flip⁻¹ A f(g)) = ∫_{U'} ℓ(f(w_{m,n} u' g)) du'`. -/
theorem shahidiIntertwining_eval :
    letI := T.topology
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (f : T.shahidiSourceDomain hm hn s π₁ π₂ μ)
      (g : GeneralLinear (m + n) F.Carrier) (ℓ : SmoothDual (pairRepresentation hm hn π₁ π₂)),
      ℓ.val (pairFlip.symm (T.shahidiTargetEval hm hn s π₁ π₂
          (T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂ f) g)) =
        ∫ a, ℓ.val (T.shahidiSourceEval hm hn s π₁ π₂ f.val
          (blockWeyl m n F.Carrier * intertwiningUnipotent m n F.Carrier a * g)) ∂μ := by
  let := T.topology
  let := T.shahidiTopologicalRing
  let := T.leviTopologicalGroup (twoBlocks m n hm hn)
  intro hπ₁ hπ₂ f g ℓ
  exact swappedOperator_eval hm hn _ hπ₁ hπ₂ _ _ hμ f g ℓ

/-- The p-adic `A(s, π, w_{m,n})` intertwines `I(s, π₁ ⊗ π₂)` with `I(-s, π₂ ⊗ π₁)` on its
domain. -/
theorem shahidiIntertwining_shahidiSource :
    letI := T.topology
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (f : T.shahidiSourceDomain hm hn s π₁ π₂ μ)
      (g : GeneralLinear (m + n) F.Carrier),
      T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂
          ⟨T.shahidiSource hm hn s π₁ π₂ g f.val,
            T.shahidiSource_mem_shahidiSourceDomain hm hn s π₁ π₂ μ f.property g⟩ =
        T.shahidiTarget hm hn s π₁ π₂ g (T.shahidiIntertwining hm hn s π₁ π₂ hμ hπ₁ hπ₂ f) := by
  let := T.topology
  let := T.shahidiTopologicalRing
  let := T.leviTopologicalGroup (twoBlocks m n hm hn)
  intro hπ₁ hπ₂ f g
  exact swappedOperator_smoothInduced hm hn _ hπ₁ hπ₂ _ _ hμ f g

end Measure

end Langlands.PadicField.TopologicalData
