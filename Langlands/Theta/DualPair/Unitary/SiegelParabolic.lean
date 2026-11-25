import Langlands.Theta.DualPair.LerayCharacter
import Langlands.Theta.DualPair.Unitary.Schrodinger
import Langlands.Group.Unitary.BigCell
/-!
# The operators of the Siegel parabolic

GKT Lemma 2.16 (p. 58) and Corollary 2.18 (p. 60) for the image `g ⊗ 1_V` of the Siegel parabolic of
`U(ν, ν)`, multiplied by the value `β(m(a) n(b)) = χ(det a)` of the Leray splitting
(Proposition 12.29, p. 375): the first two formulas of Proposition 12.27 (1) (p. 372) in Case `3₊`.
For `g = [[A, B], [0, D]]` in the Siegel parabolic subgroup of `U(ν, ν)`, the Leray splitting acts
on Schwartz–Bruhat functions on `M_{α×ν}(E)` by

`siegelParabolicOp c ψ χ Q g φ x = splittingScalar F χ |α| (det A) · ψ(½ β(x A, x B)) · φ(x A)`,

with `β = hermitianPairing c Q`. The internal lemmas prove that these operators form a
representation of the Siegel parabolic (`parFun_sieg_mul`), preserve Schwartz–Bruhat functions
(`parFun_mem`) and the `L²` norm for every Haar measure (`parFun_lintegral_sq`, through
`map_mul_mul_addHaar`), normalize the Schrödinger operators along `w ↦ w g` (`heisFun_parFun`), and
fix a given Schwartz–Bruhat function for `g` near `1` (`parFun_fixed_near_one`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

namespace Unitary.Internal

end Unitary.Internal

open Unitary.Internal

section ParFunDef

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The operator `φ ↦ splittingScalar (det A) ψ(½ β(x A, x B)) φ(x A)` of `g = [[A, B], [C, D]]`;
it is used for `g` in the Siegel parabolic (`C = 0`). -/
def siegelParabolicOp (ψ : AddChar F ℂ) (χ : Eˣ →* Circle) (Q : Matrix α α E) (g : Matrix (ν ⊕ ν)
    (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => splittingScalar F χ (Fintype.card α) g.toBlocks₁₁.det *
    (ψ (2⁻¹ * pr c Q (x * g.toBlocks₁₁) (x * g.toBlocks₁₂)) * φ (x * g.toBlocks₁₁))

end ParFunDef

namespace Unitary.Internal

theorem parFun_sieg_mul : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)), (∀ φ : Matrix α ν E → ℂ,
    siegelParabolicOp c ψ χ Q (mat c (1 : ofForm c (hyperbolicForm ν E))) φ = φ) ∧
    ∀ p ∈ siegelParabolic c ν, ∀ q ∈ siegelParabolic c ν, ∀ φ : Matrix α ν E → ℂ,
    siegelParabolicOp c ψ χ Q (mat c (p * q)) φ = siegelParabolicOp c ψ χ Q (mat c p)
    (siegelParabolicOp c ψ χ Q (mat c q) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχ hres
  obtain ⟨β, hβ, hsymm, -, hadj, -⟩ := pr_alg F E c δ hE α ν Q hQ
  obtain ⟨hsc1, hscmul, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hres
  refine ⟨?_, ?_⟩
  · intro φ
    funext x
    have h1 : mat c (1 : ofForm c (hyperbolicForm ν E)) = 1 := rfl
    have h11 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
      ext i j; simp [toBlocks₁₁, one_apply]
    have h12 : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
      ext i j; simp [toBlocks₁₂, one_apply]
    have hp0 : pr c Q x 0 = 0 := by rw [← hβ]; simp
    simp only [siegelParabolicOp, h1, h11, h12, det_one, hsc1, Matrix.mul_one, Matrix.mul_zero, hp0,
        mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro p hp q hq φ
    funext x
    have hmul : mat c (p * q) = mat c p * mat c q := rfl
    obtain ⟨hq1, -, -⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hE.involutive q hq
    have hP : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0
        (mat c p).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hp]; exact (fromBlocks_toBlocks _).symm
    have hQ' : mat c q = fromBlocks (mat c q).toBlocks₁₁ (mat c q).toBlocks₁₂ 0
        (mat c q).toBlocks₂₂ := by
      rw [← (mem_sieg c).mp hq]; exact (fromBlocks_toBlocks _).symm
    set A := (mat c p).toBlocks₁₁
    set B := (mat c p).toBlocks₁₂
    set A' := (mat c q).toBlocks₁₁
    set B' := (mat c q).toBlocks₁₂
    set D' := (mat c q).toBlocks₂₂
    have e11 : (mat c (p * q)).toBlocks₁₁ = A * A' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have e12 : (mat c (p * q)).toBlocks₁₂ = A * B' + B * D' := by
      rw [hmul, hP, hQ', fromBlocks_multiply]; simp
    have hcc : ∀ M : Matrix ν ν E, (M.map c).map c = M := fun M => by ext; simp [hE.involutive _]
    have hDA : D' * (A'.map c)ᵀ = 1 := by
      have h := congrArg (fun M : Matrix ν ν E => (M.map c)ᵀ) hq1
      have hm : ∀ M N : Matrix ν ν E, (M * N).map c = M.map c * N.map c := fun M N => by
        ext i j; simp [Matrix.mul_apply, map_sum, map_mul]
      have h1c : ((1 : Matrix ν ν E).map c)ᵀ = 1 := by
        rw [Matrix.map_one _ (map_zero c) (map_one c), transpose_one]
      simp only [hm, Matrix.transpose_map, hcc, transpose_mul, transpose_transpose, h1c] at h
      exact h
    have hadd : ∀ u v w : Matrix α ν E, pr c Q u (v + w) = pr c Q u v + pr c Q u w := by
      intro u v w; rw [← hβ, ← hβ, ← hβ, map_add]
    have hkey : pr c Q (x * A * A') (x * B * D') = pr c Q (x * A) (x * B) := by
      rw [← hβ, ← hβ, hadj, Matrix.mul_assoc (x * B), hDA, Matrix.mul_one]
    simp only [siegelParabolicOp, e11, e12, det_mul, hscmul, Matrix.mul_add, ← Matrix.mul_assoc,
        hadd, hkey, mul_add,
      AddChar.map_add_eq_mul]
    ring



theorem parFun_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) (p : ofForm c (hyperbolicForm ν E)),
    p ∈ siegelParabolic c ν → ∀ φ ∈ schwartzBruhatSubmodule (Matrix α ν E),
    siegelParabolicOp c ψ χ Q (mat c p) φ ∈ schwartzBruhatSubmodule (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ _ p hp φ hφ
  have hring : IsTopologicalRing E := hE.isTopologicalRing
  have hc : Continuous c := hE.continuous_conj
  have htr : Continuous (Algebra.trace F E) := hE.continuous_trace
  obtain ⟨β, hβ, -, -, -, hform⟩ := pr_alg F E c δ hE α ν Q hQ
  obtain ⟨hinv, -, -⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hE.involutive p hp
  set a := (mat c p).toBlocks₁₁ with ha
  set b := (mat c p).toBlocks₁₂ with hb
  set d := (((mat c p).toBlocks₂₂).map c)ᵀ with hd
  have hinv' : d * a = 1 := mul_eq_one_comm.mp hinv
  have hca : Continuous fun x : Matrix α ν E => x * a := continuous_id.matrix_mul continuous_const
  have hcb : Continuous fun x : Matrix α ν E => x * b := continuous_id.matrix_mul continuous_const
  have hcd : Continuous fun x : Matrix α ν E => x * d := continuous_id.matrix_mul continuous_const
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * a
      invFun := fun x => x * d
      left_inv := fun x => by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
      continuous_toFun := hca
      continuous_invFun := hcd }
  have hpr : Continuous fun x : Matrix α ν E => (2⁻¹ : F) * pr c Q (x * a) (x * b) := by
    refine continuous_const.mul ?_
    have : (fun x : Matrix α ν E => pr c Q (x * a) (x * b)) = fun x =>
        2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * ((x * a) * ((x * b).map c)ᵀ))) := by
      funext x; rw [← hβ, hform]
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_const.matrix_mul
      (hca.matrix_mul (hcb.matrix_map hc).matrix_transpose)).matrix_trace)
  have h1 := (isLocallyConstant_of_continuous_addChar ψ hψ).comp_continuous hpr
  have h2 : IsLocallyConstant (φ ∘ fun x : Matrix α ν E => x * a) := hφ.1.comp_continuous hca
  have h3 : HasCompactSupport (φ ∘ e) := hφ.2.comp_homeomorph e
  refine ⟨(IsLocallyConstant.const _).mul (h1.mul h2), ?_⟩
  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left h3)




theorem heisFun_parFun : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) (p : ofForm c (hyperbolicForm ν E)),
    p ∈ siegelParabolic c ν → ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ),
    heisFun c ψ Q w (siegelParabolicOp c ψ χ Q (mat c p) φ) = siegelParabolicOp c ψ χ Q (mat c p)
    (heisFun c ψ Q (w * mat c p) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ _ χ _ _ p hp w φ
  have hc : ∀ z, c (c z) = z := hE.involutive
  have hp0 : (mat c p).toBlocks₂₁ = 0 := hp
  set A := (mat c p).toBlocks₁₁ with hA
  set B := (mat c p).toBlocks₁₂ with hB
  set D := (mat c p).toBlocks₂₂ with hD
  have key : ∀ x y : Matrix α ν E, fromCols x y * mat c p = fromCols (x * A) (x * B + y * D) := by
    intro x y
    conv_lhs => rw [← fromBlocks_toBlocks (mat c p)]
    rw [fromCols_mul_fromBlocks, hp0]
    simp [hA, hB, hD]
  have spl : ∀ u v : Matrix α ν E, fromCols u v = fromCols u 0 + fromCols 0 v := fun u v => by
    ext i (j | j) <;> simp
  have e1 : ∀ x x' : Matrix α ν E,
      fromCols (x + x') (0 : Matrix α ν E) = fromCols x 0 + fromCols x' 0 := fun x x' => by
    ext i (j | j) <;> simp
  have e2 : ∀ y y' : Matrix α ν E,
      fromCols (0 : Matrix α ν E) (y + y') = fromCols 0 y + fromCols 0 y' := fun x x' => by
    ext i (j | j) <;> simp

  have h1 : ∀ x y : Matrix α ν E,
      hermitianSymplecticForm c Q (fromCols (x * A) 0) (fromCols 0
      (y * D)) = hermitianSymplecticForm c Q (fromCols x 0) (fromCols 0 y) := by
    intro x y
    have h := form_mul c Q p (fromCols x 0) (fromCols 0 y)
    change hermitianSymplecticForm c Q (fromCols x 0 * mat c p) (fromCols 0 y * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero, zero_add] at h
    rw [spl (x * A) (x * B), form_add_left, form_right_right, add_zero] at h
    exact h

  have h2 : ∀ x x' : Matrix α ν E,
      hermitianSymplecticForm c Q (fromCols (x' * A) 0) (fromCols 0
      (x * B)) = hermitianSymplecticForm c Q (fromCols (x * A) 0) (fromCols 0 (x' * B)) := by
    intro x x'
    have h := form_mul c Q p (fromCols x' 0) (fromCols x 0)
    change hermitianSymplecticForm c Q (fromCols x' 0 * mat c p) (fromCols x 0 * mat c p) = _ at h
    rw [key, key] at h
    simp only [Matrix.zero_mul, add_zero] at h
    rw [spl (x' * A) (x' * B), spl (x * A) (x * B), form_add_left, form_add_right, form_add_right,
      form_left_left, form_left_left, form_right_right,
          form_swap c hc hQ.1 (fromCols (x * A) 0) (fromCols 0 (x' * B))] at h
    linear_combination h
  have hw : w * mat c p = fromCols (w.toCols₁ * A) (w.toCols₁ * B + w.toCols₂ * D) := by
    conv_lhs => rw [← fromCols_toCols w]
    exact key _ _
  funext x
  simp only [heisFun, siegelParabolicOp, pr, hw, toCols₁_fromCols, toCols₂_fromCols]
  rw [← hA, ← hB]
  have key2 : ∀ (a b c d : F) (s t : ℂ),
      a + b = c + d → ψ a * (s * (ψ b * t)) = s * (ψ c * (ψ d * t)) := by
    intro a b c d s t h
    rw [show ψ a * (s * (ψ b * t)) = s * (ψ (a + b) * t) by rw [AddChar.map_add_eq_mul]; ring, h,
      AddChar.map_add_eq_mul]
    ring
  rw [Matrix.add_mul x w.toCols₁ A, Matrix.add_mul x w.toCols₁ B]
  simp only [e1, e2, form_add_left, form_add_right, h1]
  rw [h2 x w.toCols₁]
  apply key2
  ring




theorem parFun_lintegral_sq : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (p : ofForm c (hyperbolicForm ν E)),
    p ∈ siegelParabolic c ν → ∀ φ : Matrix α ν E → ℂ, ∫⁻ x,
    ‖siegelParabolicOp c ψ χ Q (mat c p) φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ _ hψ1 _ χ _ hres _ _ μ _ p hp φ
  obtain ⟨h1, -, -⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hE.involutive p hp
  have hfd : FiniteDimensional F E := hE.finite
  have htop : IsTopologicalRing E := hE.isTopologicalRing
  have := hfd
  obtain ⟨-, -, -, hnorm, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hres
  have h1' := mul_eq_one_comm.mp h1
  let A : GL ν E := ⟨(mat c p).toBlocks₁₁, _, h1, h1'⟩
  have hA : ((A : GL ν E) : Matrix ν ν E) = (mat c p).toBlocks₁₁ := rfl
  set D : NNReal := distribHaarChar F ((Units.map (Algebra.norm F : E →* F))
      (Matrix.GeneralLinearGroup.det A)) with hD
  have hD0 : D ≠ 0 := distribHaarChar_pos.ne'
  have hsc : ‖splittingScalar F χ (Fintype.card α) (mat c p).toBlocks₁₁.det‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) := by
    have := hnorm (Matrix.GeneralLinearGroup.det A)
    have hd : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = (mat c p).toBlocks₁₁.det := rfl
    rw [hd] at this
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.eq
    push_cast
    rw [this]
  have hpt : ∀ x, ‖siegelParabolicOp c ψ χ Q (mat c p) φ x‖ₑ ^ 2 =
      ((D ^ Fintype.card α : NNReal) : ENNReal) * ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 := by
    intro x
    have hψe : ∀ t, ‖ψ t‖ₑ = 1 := fun t => by
      rw [enorm_eq_nnnorm]; simp [← NNReal.coe_eq_one, coe_nnnorm, hψ1 t]
    simp only [siegelParabolicOp, enorm_mul, hψe, one_mul, mul_pow, hsc, hA]
  have := htop
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * (A : Matrix ν ν E)
      invFun := fun x => x * ((A⁻¹ : GL ν E) : Matrix ν ν E)
      left_inv := fun x => by simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      continuous_toFun := Continuous.matrix_mul continuous_id continuous_const
      continuous_invFun := Continuous.matrix_mul continuous_id continuous_const }
  have hmap : μ.map (e.toMeasurableEquiv) = ((D ^ Fintype.card α)⁻¹ : NNReal) • μ := by
    have := map_mul_mul_addHaar (F := F) μ 1 A
    have hf : (fun x : Matrix α ν E => ((1 : GL α E) : Matrix α α E) * x *
        (A : Matrix ν ν E)) = e.toMeasurableEquiv := by
      funext x; simp [e]
    rw [hf] at this
    rw [this, ← hD]
    simp
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  have hl := lintegral_map_equiv (fun y => ‖φ y‖ₑ ^ 2) e.toMeasurableEquiv (μ := μ)
  have hl' : ∫⁻ x, ‖φ (x * (A : Matrix ν ν E))‖ₑ ^ 2 ∂μ = ∫⁻ y,
      ‖φ y‖ₑ ^ 2 ∂(μ.map e.toMeasurableEquiv) := hl.symm
  rw [hl', hmap, lintegral_smul_measure, ENNReal.smul_def,
      smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hD0), ENNReal.coe_one, one_mul]



namespace ParNear

variable {E : Type} [Field E] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero (M N : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
    (h : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h, fromBlocks_multiply]
  simp

omit [Fintype ν] in
theorem toBlocks₁₁_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₁ = 1 := by
  ext i j; simp [toBlocks₁₁, one_apply]

omit [Fintype ν] in
theorem toBlocks₁₂_one' : (1 : Matrix (ν ⊕ ν) (ν ⊕ ν) E).toBlocks₁₂ = 0 := by
  ext i j; simp [toBlocks₁₂, one_apply]

variable {F : Type} [Field F] [Algebra F E] (c : E →ₐ[F] E) {α : Type} [Fintype α] [DecidableEq α]

theorem mat_one : mat c (1 : ofForm c (hyperbolicForm ν E)) = 1 := rfl

theorem mat_mul_mat_inv (g : ofForm c (hyperbolicForm ν E)) : mat c g * mat c g⁻¹ = 1 := by
  change (((g * g⁻¹ : ofForm c (hyperbolicForm ν E)) : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = 1
  rw [mul_inv_cancel]; rfl

omit [DecidableEq α] in
theorem pr_zero_right (Q : Matrix α α E) (x : Matrix α ν E) : pr c Q x 0 = 0 := by
  simp [pr, hermitianSymplecticForm, hermitianTensor]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing E]

omit [TopologicalSpace F] [IsTopologicalRing E] in
theorem continuous_mat : Continuous fun g : ofForm c (hyperbolicForm ν E) => mat c g :=
  Units.continuous_val.comp continuous_subtype_val

omit [TopologicalSpace F] [IsTopologicalRing E] in
theorem continuous_mat_inv : Continuous fun g : ofForm c (hyperbolicForm ν E) => mat c g⁻¹ :=
  Units.continuous_coe_inv.comp continuous_subtype_val

omit [DecidableEq α] in
theorem continuous_pr (hc : Continuous c) (htr : Continuous (Algebra.trace F E)) [ContinuousMul F]
    (Q : Matrix α α E) :
    Continuous fun p : Matrix α ν E × Matrix α ν E => pr c Q p.1 p.2 := by
  simp only [pr, hermitianSymplecticForm, hermitianTensor]
  refine continuous_const.mul (htr.comp
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ => ?_))
  refine Continuous.mul (Continuous.mul (Continuous.mul ?_ continuous_const) continuous_const)
      (hc.comp ?_)
  · rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact continuous_const
  · rcases l with l | l
    · exact continuous_const
    · exact continuous_snd.matrix_elem k l

omit [DecidableEq α] in
theorem continuous_pr_comp (hc : Continuous c) (htr : Continuous (Algebra.trace F E))
    [ContinuousMul F] (Q : Matrix α α E)
    {X : Type} [TopologicalSpace X] {f g : X → Matrix α ν E} (hf : Continuous f)
        (hg : Continuous g) :
    Continuous fun x => pr c Q (f x) (g x) := by
  have h := (continuous_pr (ν := ν) c hc htr Q).comp (hf.prodMk hg)
  exact h

end ParNear

open ParNear

theorem parFun_fixed_near_one : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E]
    [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E)
    (_ : IsQuadraticInvolution c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ :
    ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)), ∀ φ ∈ schwartzBruhatSubmodule (Matrix α ν E),
    ∀ᶠ g in nhds (1 : ofForm c (hyperbolicForm ν E)),
    g ∈ siegelParabolic c ν → siegelParabolicOp c ψ χ Q (mat c g) φ = φ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q _ ψ hψ _ _ χ hχ _ φ hφ
  have htop : IsTopologicalRing E := hE.isTopologicalRing
  have hcc : Continuous c := hE.continuous_conj
  have htr : Continuous (Algebra.trace F E) := hE.continuous_trace
  have := htop
  have hψl := isLocallyConstant_of_continuous_addChar ψ hψ
  have hφl : IsLocallyConstant φ := hφ.1
  have hK : IsCompact (tsupport φ) := hφ.2
  have hA : Continuous fun g : ofForm c (hyperbolicForm ν E) => (mat c g).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_mat c).matrix_elem _ _
  have hB : Continuous fun g : ofForm c (hyperbolicForm ν E) => (mat c g).toBlocks₁₂ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_mat c).matrix_elem _ _
  have hA' : Continuous fun g : ofForm c (hyperbolicForm ν E) => (mat c g⁻¹).toBlocks₁₁ :=
    continuous_pi fun i => continuous_pi fun j => (continuous_mat_inv c).matrix_elem _ _

  have hi : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)),
      splittingScalar F χ (Fintype.card α) (mat c g).toBlocks₁₁.det = 1 := by
    have ht : Tendsto (fun g : ofForm c (hyperbolicForm ν E) => (mat c g).toBlocks₁₁.det) (𝓝 1)
        (𝓝 1) := by
      have := hA.matrix_det.tendsto 1
      rwa [mat_one, toBlocks₁₁_one', det_one] at this
    exact ht.eventually (sc_eventually_eq_one F E c δ hE _ χ hχ)

  have hii : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)), ∀ x ∈ tsupport φ,
      ψ (2⁻¹ * pr c Q (x * (mat c g).toBlocks₁₁) (x * (mat c g).toBlocks₁₂)) * φ (x *
          (mat c g).toBlocks₁₁) = φ x := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have hP : Continuous fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E =>
        pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_pr_comp c hcc htr Q (continuous_snd.matrix_mul (hA.comp continuous_fst))
        (continuous_snd.matrix_mul (hB.comp continuous_fst))
    have hP2 : Continuous fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E =>
        (2 : F)⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂) :=
      continuous_const.mul hP
    have h1 : IsLocallyConstant fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E =>
        ψ (2⁻¹ * pr c Q (p.2 * (mat c p.1).toBlocks₁₁) (p.2 * (mat c p.1).toBlocks₁₂)) :=
      hψl.comp_continuous hP2
    have h2 : IsLocallyConstant fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E => φ (p.2 *
        (mat c p.1).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x), h3.eventually_eq (1,
        x)] with p e1 e2 e3
    rw [e1, e2, e3, mat_one, toBlocks₁₁_one', toBlocks₁₂_one', Matrix.mul_one, Matrix.mul_zero,
      pr_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul]

  have hiii : ∀ᶠ g in 𝓝 (1 : ofForm c (hyperbolicForm ν E)), ∀ y ∈ tsupport φ,
      φ (y * (mat c g⁻¹).toBlocks₁₁) = φ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h2 : IsLocallyConstant fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E => φ (p.2 *
        (mat c p.1⁻¹).toBlocks₁₁) :=
      hφl.comp_continuous (continuous_snd.matrix_mul (hA'.comp continuous_fst))
    have h3 : IsLocallyConstant fun p : ofForm c (hyperbolicForm ν E) × Matrix α ν E => φ p.2 :=
      hφl.comp_continuous continuous_snd
    filter_upwards [h2.eventually_eq (1, y), h3.eventually_eq (1, y)] with p e2 e3
    rw [e2, e3, inv_one, mat_one, toBlocks₁₁_one', Matrix.mul_one]
  filter_upwards [hi, hii, hiii] with g hg1 hg2 hg3 hg
  have hinv : (mat c g).toBlocks₁₁ * (mat c g⁻¹).toBlocks₁₁ = 1 := by
    rw [← toBlocks₁₁_mul_of_toBlocks₂₁_eq_zero _ _ ((mem_sieg c).mp
        ((siegelParabolic c ν).inv_mem hg)),
      mat_mul_mat_inv, toBlocks₁₁_one']
  funext x
  simp only [siegelParabolicOp]
  rw [hg1, one_mul]
  by_cases hx : x ∈ tsupport φ
  · exact hg2 x hx
  · rw [image_eq_zero_of_notMem_tsupport hx]
    by_contra hne
    have hne' : φ (x * (mat c g).toBlocks₁₁) ≠ 0 := right_ne_zero_of_mul hne
    have hy : x * (mat c g).toBlocks₁₁ ∈ tsupport φ := subset_tsupport _ hne'
    have e := hg3 _ hy
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one] at e
    exact hx (subset_tsupport _ (by rw [Function.mem_support, e]; exact hne'))


end Unitary.Internal

end Langlands.Theta
