import Langlands.Representation.Shahidi.IntertwiningPadic
import Langlands.Representation.Shahidi.LocalCoefficient

/-!
# Shahidi's local coefficient over a p-adic field

The relation (0.3) between the Jacquet functionals of the p-adic `I(s, π₁ ⊗ π₂)` and
`I(-s, π₂ ⊗ π₁)` and the intertwining operator `A(s, π, w_{m,n})`, for the functional
`λ₁ ⊗ λ₂` built from standard Whittaker functionals `λ₁` of `π₁` and `λ₂` of `π₂`: the
relation that a rational function of `q^(-s)` is the local coefficient, for fixed
functionals and for all admissible choices, and its uniqueness.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.Shahidi

open HarmonicAnalysis

universe uV

section PairFunctional

variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]

/-- The functionals `λ₁` on the factor `0` and `λ₂` on the factor `1` of the two-factor
carrier. -/
def pairFactorFunctional (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    ∀ i : Fin 2, pairCarrier V₁ V₂ i →ₗ[ℂ] ℂ
  | 0 => ℓ₁
  | 1 => ℓ₂

/-- The functional `λ₁ ⊗ λ₂ : v₁ ⊗ v₂ ↦ λ₁(v₁) λ₂(v₂)` on the two-factor tensor
carrier `V₁ ⊗ V₂`: the linear map induced by the multilinear map
`v ↦ λ₁(v₀) λ₂(v₁)`. -/
def pairFunctional (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    PiTensorProduct ℂ (pairCarrier V₁ V₂) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ (Fin 2) ℂ).compLinearMap (pairFactorFunctional ℓ₁ ℓ₂))

theorem pairFunctional_tprod (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (v : ∀ i, pairCarrier V₁ V₂ i) :
    pairFunctional ℓ₁ ℓ₂ (PiTensorProduct.tprod ℂ v) =
      pairFactorFunctional ℓ₁ ℓ₂ 0 (v 0) * pairFactorFunctional ℓ₁ ℓ₂ 1 (v 1) := by
  rw [pairFunctional, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two]

@[simp]
theorem pairFunctional_pairTensor (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) (v₁ : V₁) (v₂ : V₂) :
    pairFunctional ℓ₁ ℓ₂ (pairTensor v₁ v₂) = ℓ₁ v₁ * ℓ₂ v₂ :=
  pairFunctional_tprod ℓ₁ ℓ₂ (pairVector v₁ v₂)

/-- `(λ₂ ⊗ λ₁)(flip x) = (λ₁ ⊗ λ₂)(x)`. -/
theorem pairFunctional_pairFlip (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (x : PiTensorProduct ℂ (pairCarrier V₁ V₂)) :
    pairFunctional ℓ₂ ℓ₁ (pairFlip x) = pairFunctional ℓ₁ ℓ₂ x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    have h : pairFlip (PiTensorProduct.tprod ℂ v) =
        PiTensorProduct.tprod ℂ (pairVector (V₁ := V₂) (V₂ := V₁) (v 1) (v 0)) :=
      pairSwap_tprod (V := pairCarrier V₁ V₂) (W := pairCarrier V₂ V₁)
        (LinearEquiv.refl ℂ V₁) (LinearEquiv.refl ℂ V₂) v _ rfl rfl
    rw [map_smul, map_smul, map_smul, h, pairFunctional_tprod, pairFunctional_tprod]
    exact congrArg (r • ·) (mul_comm _ _)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem pairFunctional_smul_left (a : ℂ) (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    pairFunctional (a • ℓ₁) ℓ₂ = a • pairFunctional ℓ₁ ℓ₂ := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  change pairFunctional (a • ℓ₁) ℓ₂ (PiTensorProduct.tprod ℂ v) =
    a • pairFunctional ℓ₁ ℓ₂ (PiTensorProduct.tprod ℂ v)
  rw [pairFunctional_tprod, pairFunctional_tprod]
  show (a • ℓ₁) (v 0) * ℓ₂ (v 1) = a • (ℓ₁ (v 0) * ℓ₂ (v 1))
  exact mul_assoc a (ℓ₁ (v 0)) (ℓ₂ (v 1))

theorem pairFunctional_smul_right (b : ℂ) (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) :
    pairFunctional ℓ₁ (b • ℓ₂) = b • pairFunctional ℓ₁ ℓ₂ := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  change pairFunctional ℓ₁ (b • ℓ₂) (PiTensorProduct.tprod ℂ v) =
    b • pairFunctional ℓ₁ ℓ₂ (PiTensorProduct.tprod ℂ v)
  rw [pairFunctional_tprod, pairFunctional_tprod]
  show ℓ₁ (v 0) * (b • ℓ₂) (v 1) = b • (ℓ₁ (v 0) * ℓ₂ (v 1))
  exact mul_left_comm (ℓ₁ (v 0)) b (ℓ₂ (v 1))

/-- Reading `V₂ ⊗ V₁`-valued functions through `flip⁻¹` turns the swapped Jacquet
integrand of `λ₁ ⊗ λ₂` into that of `λ₂ ⊗ λ₁`. -/
theorem swappedJacquetIntegrand_pairFlip_symm {F : Type*} [Field F] [TopologicalSpace F]
    (m n : ℕ) (ψ : UnitaryAdditiveCharacter F) (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
    (B : GeneralLinear (m + 1 + (n + 1)) F → PiTensorProduct ℂ (pairCarrier V₂ V₁)) :
    swappedJacquetIntegrand m n ψ (pairFunctional ℓ₁ ℓ₂) (fun g => pairFlip.symm (B g)) =
      swappedJacquetIntegrand m n ψ (pairFunctional ℓ₂ ℓ₁) B := by
  funext a
  simp only [swappedJacquetIntegrand_apply]
  rw [← pairFunctional_pairFlip ℓ₁ ℓ₂, LinearEquiv.apply_symm_apply]

end PairFunctional

end Langlands.Shahidi

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi GeneralLinear MeasureTheory HarmonicAnalysis Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem localCoefficientTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

variable {m n : ℕ}
variable {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
variable (π₁ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V₁)
  (π₂ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V₂)

/-- The functions `g ↦ f(g) ∈ V₁ ⊗ V₂` of the p-adic `I(s, π₁ ⊗ π₂)` on
`GL_{(m+1)+(n+1)}`. -/
def shahidiSourceFunctions (s : ℂ) :
    Set (GeneralLinear (m + 1 + (n + 1)) F.Carrier → PiTensorProduct ℂ (pairCarrier V₁ V₂)) :=
  Set.range (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂)

variable [MeasurableSpace F.Carrier]

/-- `C` is Shahidi's local coefficient `C_χ(s, π₁ ⊗ π₂)` for the fixed standard Whittaker
functionals `λ₁` of `π₁` and `λ₂` of `π₂`: the generic `IsLocalCoefficient` for the
p-adic `I(s, π₁ ⊗ π₂)`, the functional `λ₁ ⊗ λ₂` on both sides (the target functional
`λ₂ ⊗ λ₁` of `I(-s, π₂ ⊗ π₁)` read through `flip⁻¹`, see
`satisfiesLocalCoefficientEquation_shahidiSourceEval_iff`), the measure `μ` of (0.1),
the measures `μJ`, `μJ'` of the two Jacquet integrals, and `q` the residue cardinality. -/
def IsShahidiLocalCoefficientFor
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (μ μJ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier))
    (μJ' : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier))
    (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ) (C : RatFunc ℂ) : Prop :=
  letI := T.topology
  letI := T.localCoefficientTopologicalRing
  IsLocalCoefficient m n ψ (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂)
    (pairFunctional ℓ₁ ℓ₂) (pairFunctional ℓ₁ ℓ₂) μ μJ μJ' T.residueCardinality
    (fun s => T.shahidiSourceFunctions π₁ π₂ s) C

/-- `C` is Shahidi's local coefficient `C_χ(s, π₁ ⊗ π₂)`, quantified over the admissible
choices: `π₁` and `π₂` have nonzero standard Whittaker functionals, and `C` is the local
coefficient for every choice of nonzero standard Whittaker functionals `λ₁` of `π₁` and
`λ₂` of `π₂`. -/
def IsShahidiLocalCoefficient
    (ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier)
    (μ μJ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier))
    (μJ' : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier)) (C : RatFunc ℂ) : Prop :=
  letI := T.topology
  (∃ ℓ₁ ∈ glFunctionals ψ m π₁, ∃ ℓ₂ ∈ glFunctionals ψ n π₂, ℓ₁ ≠ 0 ∧ ℓ₂ ≠ 0) ∧
    ∀ ℓ₁ ∈ glFunctionals ψ m π₁, ∀ ℓ₂ ∈ glFunctionals ψ n π₂, ℓ₁ ≠ 0 → ℓ₂ ≠ 0 →
      T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C

variable {T π₁ π₂}
variable {ψ : letI := T.topology; UnitaryAdditiveCharacter F.Carrier}
  {μ μJ : Measure (Matrix (Fin (n + 1)) (Fin (m + 1)) F.Carrier)}
  {μJ' : Measure (Matrix (Fin (m + 1)) (Fin (n + 1)) F.Carrier)}

/-- For fixed functionals, the local coefficient is unique. -/
theorem IsShahidiLocalCoefficientFor.unique :
    letI := T.topology
    ∀ (_ : IsSmooth π₁) (_ : IsSmooth π₂) {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ}
      {C C' : RatFunc ℂ},
      T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C →
      T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C' → C = C' := by
  let := T.topology
  let := T.localCoefficientTopologicalRing
  let := T.leviTopologicalGroup (twoBlocks (m + 1) (n + 1) (Nat.add_one_pos m)
    (Nat.add_one_pos n))
  intro hπ₁ hπ₂ ℓ₁ ℓ₂ C C' h h'
  exact IsLocalCoefficient.unique (T.leviCompactOpenCofinal _)
    (isSmooth_pairRepresentation _ _ hπ₁ hπ₂) T.residueCardinality_gt_one h h'

/-- The local coefficient is unique. -/
theorem IsShahidiLocalCoefficient.unique :
    letI := T.topology
    ∀ (_ : IsSmooth π₁) (_ : IsSmooth π₂) {C C' : RatFunc ℂ},
      T.IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C →
      T.IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C' → C = C' := by
  let := T.topology
  intro hπ₁ hπ₂ C C' h h'
  obtain ⟨⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, h₁, h₂⟩, hC⟩ := h
  exact IsShahidiLocalCoefficientFor.unique hπ₁ hπ₂ (hC ℓ₁ hℓ₁ ℓ₂ hℓ₂ h₁ h₂)
    (h'.2 ℓ₁ hℓ₁ ℓ₂ hℓ₂ h₁ h₂)

/-- Rescaling the functionals by nonzero scalars preserves the local coefficient. -/
theorem IsShahidiLocalCoefficientFor.smul {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ}
    {C : RatFunc ℂ} (h : T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C)
    {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' (a • ℓ₁) (b • ℓ₂) C := by
  let := T.topology
  let := T.localCoefficientTopologicalRing
  have := IsLocalCoefficient.smul h (mul_ne_zero hb ha)
  unfold IsShahidiLocalCoefficientFor
  simpa only [pairFunctional_smul_left, pairFunctional_smul_right, smul_smul] using this

/-- Under multiplicity one of the standard Whittaker functionals, the local coefficient for
one choice of nonzero functionals is the local coefficient for all admissible choices. -/
theorem IsShahidiLocalCoefficientFor.isShahidiLocalCoefficient :
    letI := T.topology
    ∀ {ℓ₁ : V₁ →ₗ[ℂ] ℂ} {ℓ₂ : V₂ →ₗ[ℂ] ℂ} {C : RatFunc ℂ},
      T.IsShahidiLocalCoefficientFor π₁ π₂ ψ μ μJ μJ' ℓ₁ ℓ₂ C →
      ℓ₁ ∈ glFunctionals ψ m π₁ → ℓ₂ ∈ glFunctionals ψ n π₂ → ℓ₁ ≠ 0 → ℓ₂ ≠ 0 →
      (∀ ℓ ∈ glFunctionals ψ m π₁, ∃ a : ℂ, ℓ = a • ℓ₁) →
      (∀ ℓ ∈ glFunctionals ψ n π₂, ∃ b : ℂ, ℓ = b • ℓ₂) →
      T.IsShahidiLocalCoefficient π₁ π₂ ψ μ μJ μJ' C := by
  let := T.topology
  intro ℓ₁ ℓ₂ C h hℓ₁ hℓ₂ h₁ h₂ hmult₁ hmult₂
  refine ⟨⟨ℓ₁, hℓ₁, ℓ₂, hℓ₂, h₁, h₂⟩, fun ℓ hℓ ℓ' hℓ' h₀ h₀' => ?_⟩
  obtain ⟨a, rfl⟩ := hmult₁ ℓ hℓ
  obtain ⟨b, rfl⟩ := hmult₂ ℓ' hℓ'
  have ha : a ≠ 0 := by
    rintro rfl
    exact h₀ (zero_smul ℂ ℓ₁)
  have hb : b ≠ 0 := by
    rintro rfl
    exact h₀' (zero_smul ℂ ℓ₂)
  exact IsShahidiLocalCoefficientFor.smul h ha hb

section Literal

variable [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier] [μ.IsAddLeftInvariant]

/-- Equation (0.3) for `f ∈ I(s, π₁ ⊗ π₂)` in the convergence domain, read literally:
the generic relation at `f` with the functional `λ₁ ⊗ λ₂` on both sides holds exactly when
`c ≠ 0`, the Jacquet integral of `f` for `λ₁ ⊗ λ₂` stabilizes to `z`, the swapped Jacquet
integral of `A f ∈ I(-s, π₂ ⊗ π₁)` for `λ₂ ⊗ λ₁` stabilizes to `z'`, and `z' = c⁻¹ z`. -/
theorem satisfiesLocalCoefficientEquation_shahidiSourceEval_iff
    (s : ℂ) (hμ : IsModulusScaling (Nat.add_one_pos m) (Nat.add_one_pos n)
      T.shahidiAbsoluteValue μ) :
    letI := T.topology
    letI := T.localCoefficientTopologicalRing
    ∀ (hπ₁ : IsSmooth π₁) (hπ₂ : IsSmooth π₂) (ℓ₁ : V₁ →ₗ[ℂ] ℂ) (ℓ₂ : V₂ →ₗ[ℂ] ℂ)
      (f : T.shahidiSourceDomain (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ μ) (c : ℂ),
      SatisfiesLocalCoefficientEquation m n ψ
          (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂)
          (pairFunctional ℓ₁ ℓ₂) (pairFunctional ℓ₁ ℓ₂) μ μJ μJ'
          (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) c ↔
        c ≠ 0 ∧ ∃ z z' : ℂ,
          HasJacquetIntegral m n ψ (pairFunctional ℓ₁ ℓ₂) μJ
            (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val) z ∧
          HasSwappedJacquetIntegral m n ψ (pairFunctional ℓ₂ ℓ₁) μJ'
            (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂
              (T.shahidiIntertwining (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ hμ
                hπ₁ hπ₂ f)) z' ∧
          z' = c⁻¹ * z := by
  let := T.topology
  let := T.localCoefficientTopologicalRing
  let := T.leviTopologicalGroup (twoBlocks (m + 1) (n + 1) (Nat.add_one_pos m)
    (Nat.add_one_pos n))
  intro hπ₁ hπ₂ ℓ₁ ℓ₂ f c
  have hA : HasIntertwiningIntegral (m + 1) (n + 1)
      (pairRepresentation (Nat.add_one_pos m) (Nat.add_one_pos n) π₁ π₂) μ
      (T.shahidiSourceEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ f.val)
      (fun g => pairFlip.symm (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s
        π₁ π₂ (T.shahidiIntertwining (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ hμ
          hπ₁ hπ₂ f) g)) :=
    fun g => T.hasIntegral_shahidiIntertwining (Nat.add_one_pos m) (Nat.add_one_pos n) s hμ
      hπ₁ hπ₂ f g
  have hswap := swappedJacquetIntegrand_pairFlip_symm m n ψ ℓ₁ ℓ₂
    (T.shahidiTargetEval (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂
      (T.shahidiIntertwining (Nat.add_one_pos m) (Nat.add_one_pos n) s π₁ π₂ hμ hπ₁ hπ₂ f))
  constructor
  · rintro ⟨hc, A, z, z', hA', hz, hz', rfl⟩
    obtain rfl := hA'.unique (T.leviCompactOpenCofinal _)
      (isSmooth_pairRepresentation _ _ hπ₁ hπ₂) hA
    refine ⟨hc, z, c⁻¹ * z, hz, ?_, rfl⟩
    unfold HasSwappedJacquetIntegral at hz' ⊢
    rwa [hswap] at hz'
  · rintro ⟨hc, z, z', hz, hz', rfl⟩
    refine ⟨hc, _, z, c⁻¹ * z, hA, hz, ?_, rfl⟩
    unfold HasSwappedJacquetIntegral at hz' ⊢
    rwa [hswap]

end Literal

end Langlands.PadicField.TopologicalData
