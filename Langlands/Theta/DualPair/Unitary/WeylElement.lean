import Langlands.Theta.DualPair.Unitary.SiegelParabolic
import Langlands.HarmonicAnalysis.Bicharacter.GaussIntegral

/-!
# The operator of the Weyl element

GKT Proposition 2.24 (p. 63: the Weyl element acts by a Fourier transform) and Theorem 1.25 (p. 34)
for the polarization of `𝕎`, and Lemma 5.1 (p. 136) tensored with `V`, in Case `3₊`. The Weyl
element of `U(ν, ν)` acts in the Leray splitting by a multiple of the Fourier transform

`hermitianFourier c ψ Q μ φ x = ∫ ψ(β(x, y)) φ(y) dμ(y)`

of the self-dual bicharacter `ψ ∘ β`, `β = hermitianPairing c Q`. The internal lemmas prove that it
intertwines the operators of the Siegel parabolic as `w p = q w` requires (`fou_parFun_levi`), that
it normalizes the Schrödinger operators along `w ↦ w J` (`heisFun_fou`), and the braid relation
`s(det(-b⁻¹)) ℱ T(n(b)) ℱ = γ T(p) ℱ T(n(-b⁻¹))` for an invertible Hermitian `b` with Gauss
integral `γ`, where `T` is `siegelParabolicOp`, `n(b) = [[1, b], [0, 1]]`,
`p = [[-b⁻¹, 1], [0, -b]]` and `s` the splitting scalar (`braid_relation`), from Weil's formula
(`bicharacterFourier_mul_bicharacterFourier`).
-/

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped Topology

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis

namespace Unitary.Internal

end Unitary.Internal

open Unitary.Internal

section FouDef

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

/-- The Fourier transform `φ ↦ (x ↦ ∫ ψ(β(x, y)) φ(y) dμ(y))` of the Hermitian pairing
`β = hermitianPairing c Q`. -/
def hermitianFourier [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ)
    (Q : Matrix α α E)
    (μ : Measure (Matrix α ν E)) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  bicharacterFourier μ (fun x y => ψ (pr c Q x y)) φ

end FouDef

namespace Unitary.Internal


theorem blocks_of_weyl_mul_eq {F : Type} [Field F] {E : Type} [Field E] [Algebra F E]
    (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : ofForm c (hyperbolicForm ν E)}
        (hp : p ∈ siegelParabolic c ν) (hq : q ∈ siegelParabolic c ν)
    (h : weylElement c ν * p = q * weylElement c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ =
        (mat c p).toBlocks₂₂ := by
  have h1 : hyperbolicForm ν E * mat c p = mat c q * hyperbolicForm ν E := congrArg (mat c) h
  rw [← fromBlocks_toBlocks (mat c p), ← fromBlocks_toBlocks (mat c q), (mem_sieg c).mp hp,
      (mem_sieg c).mp hq,
    hyperbolicForm_eq_fromBlocks, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1
  obtain ⟨h11, h12, -, h22⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h22
  · simpa using h11
  · simpa using h12.symm

theorem fou_parFun_levi : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ siegelParabolic c ν, ∀ q ∈ siegelParabolic c ν,
    weylElement c ν * p = q * weylElement c ν → ∀ φ : Matrix α ν E → ℂ,
    hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (mat c p) φ) = siegelParabolicOp c ψ χ Q
    (mat c q) (hermitianFourier c ψ Q μ φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ hχ _ _ μ _ p hp q hq hpq φ
  obtain ⟨hb, hb', ha'⟩ := blocks_of_weyl_mul_eq c hp hq hpq
  obtain ⟨had, -, -⟩ := exists_eq_siegelLevi_mul_siegelUnipotent c hE.involutive p hp
  obtain ⟨β, hβ, -, -, hadj, -⟩ := pr_alg F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, hsc, -⟩ := sc_basic F E c δ hE (Fintype.card α) χ hχ
  have hfd : FiniteDimensional F E := hE.finite
  have hring : IsTopologicalRing E := hE.isTopologicalRing
  have := hfd
  set a := (mat c p).toBlocks₁₁ with ha
  set d := (mat c p).toBlocks₂₂ with hd
  have hda : (d.map c)ᵀ * a = 1 := mul_eq_one_comm.mp had
  let A : GL ν E := ⟨a, (d.map c)ᵀ, had, hda⟩
  have hmap := map_mul_mul_addHaar (F := F) μ 1 A
  simp only [Units.val_one, Matrix.one_mul, map_one, one_pow, one_mul] at hmap
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun y => y * a
      invFun := fun y => y * (d.map c)ᵀ
      left_inv := fun y => by simp only [Matrix.mul_assoc, had, Matrix.mul_one]
      right_inv := fun y => by simp only [Matrix.mul_assoc, hda, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hdet : d.det = (c a.det)⁻¹ := by
    have h1 : a.det * c d.det = 1 := by
      have := congrArg Matrix.det had
      rw [det_mul, det_transpose, det_one] at this
      rw [← this]
      congr 1
      exact RingHom.map_det (c : E →+* E) d
    have h2 := congrArg c h1
    rw [map_mul, hE.involutive, map_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hsc' := hsc (Matrix.GeneralLinearGroup.det A)
  have hAdet : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = a.det := rfl
  rw [hAdet, ← hdet] at hsc'
  have hN : distribHaarChar F ((Units.map (Algebra.norm F : E →* F))
      (Matrix.GeneralLinearGroup.det A)) ≠ 0 :=
    (distribHaarChar_pos).ne'
  funext x
  have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by rw [← hβ, map_zero]
  have hint : ∫ y, ψ (pr c Q (x * d) (y * a)) * φ (y * a) ∂μ
      = (((distribHaarChar F ((Units.map (Algebra.norm F : E →* F))
          (Matrix.GeneralLinearGroup.det A)) ^ Fintype.card α : ℝ) : ℂ))⁻¹
        * ∫ y, ψ (pr c Q (x * d) y) * φ y ∂μ := by
    have h1 := integral_map_equiv (μ := μ) e.toMeasurableEquiv (fun y => ψ (pr c Q (x * d) y) * φ y)
    have h2 : μ.map e.toMeasurableEquiv = _ := hmap
    rw [h2, integral_smul_nnreal_measure] at h1
    refine Eq.trans h1.symm ?_
    rw [NNReal.smul_def, Complex.real_smul]
    simp [distribHaarChar]
  have hpr : ∀ y : Matrix α ν E, pr c Q (x * d) (y * a) = pr c Q x y := fun y => by
    rw [← hβ, hadj, Matrix.mul_assoc, had, Matrix.mul_one, hβ]
  simp only [hpr] at hint
  simp only [hermitianFourier, bicharacterFourier, siegelParabolicOp, hb, hb', ha', ← ha,
      Matrix.mul_zero, h0, mul_zero, AddChar.map_zero_eq_one, one_mul]
  simp only [mul_left_comm _ (splittingScalar F χ (Fintype.card α) a.det)]
  rw [integral_const_mul, hint, ← hsc', ← mul_assoc, mul_assoc (splittingScalar F χ _ d.det),
      mul_inv_cancel₀, mul_one]
  exact_mod_cast pow_ne_zero _ hN




theorem heisFun_fou : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
    (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (w : Matrix α (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ),
    heisFun c ψ Q w (hermitianFourier c ψ Q μ φ) = hermitianFourier c ψ Q μ (heisFun c ψ Q
    (w * hyperbolicForm ν E) φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ _ _ μ _ w φ
  obtain ⟨β, hβ, hsym, -, -, -⟩ := pr_alg F E c δ hE α ν Q hQ
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have hh : ∀ (w : Matrix α (ν ⊕ ν) E) (φ : Matrix α ν E → ℂ) (x : Matrix α ν E),
      heisFun c ψ Q w φ x = ψ (β x w.toCols₂ + 2⁻¹ * β w.toCols₁ w.toCols₂) * φ
          (x + w.toCols₁) := by
    intro w φ x
    show ψ (pr c Q _ _ + 2⁻¹ * pr c Q _ _) * _ = _
    rw [← hβ, ← hβ]
  have hJ : w * hyperbolicForm ν E = fromCols (-w.toCols₂) w.toCols₁ := by
    ext i (j | j) <;> simp [hyperbolicForm_eq_fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
        one_apply, fromBlocks, toCols₁, toCols₂]
  funext x
  simp only [hermitianFourier]
  rw [hh, hJ]
  simp only [bicharacterFourier, hh, toCols₁_fromCols, toCols₂_fromCols, ← hβ]
  set x₁ := w.toCols₁
  set y₁ := w.toCols₂
  rw [← integral_add_right_eq_self (μ := μ) (fun y => ψ (β x y) * (ψ (β y x₁ + 2⁻¹ * β (-y₁) x₁) * φ
      (y + -y₁))) y₁,
    ← integral_const_mul]
  congr 1
  funext y
  simp only [add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, hsym y x₁, hsym y₁ x₁]
  ring




theorem braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (_ : IsQuadraticInvolution c δ) (α : Type)
    [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E)
    (_ : IsHerm c Q) (ψ : AddChar F ℂ) (_ : Continuous ψ) (_ : ∀ t,
    ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ
    (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure
    (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ),
    (b.map c)ᵀ = b → b.det ≠ 0 → HasGaussIntegral μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ →
    ∀ φ ∈ schwartzBruhatSubmodule (Matrix α ν E),
    splittingScalar F χ (Fintype.card α) (-b⁻¹).det • hermitianFourier c ψ Q μ
    (siegelParabolicOp c ψ χ Q (fromBlocks 1 b 0 1)
    (hermitianFourier c ψ Q μ φ)) = γ • siegelParabolicOp c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b))
    (hermitianFourier c ψ Q μ (siegelParabolicOp c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hn h1 χ _ hχ _ _ μ _ b γ hb hd hG φ hφ
  have hfd : FiniteDimensional F E := hE.finite
  have hring : IsTopologicalRing E := hE.isTopologicalRing
  have : FiniteDimensional F E := hE.finite
  have : IsModuleTopology F (Matrix α ν E) := isModuleTopology_matrix F (E := E) α ν
  have := IsModuleTopology.isTopologicalAddGroup F (Matrix α ν E)
  have := t2Space_of_finiteDimensional F (Matrix α ν E)
  have := locallyCompactSpace_of_finiteDimensional F (Matrix α ν E)
  have := secondCountableTopology_of_finiteDimensional F (Matrix α ν E)
  have := compactOpenExhaustion_of_finiteDimensional F (Matrix α ν E)
  obtain ⟨β, hβ, hs, hnd, hadj, -⟩ := pr_alg F E c δ hE α ν Q hQ
  have hsc := (sc_basic F E c δ hE (Fintype.card α) χ hχ).1
  have hP := isSelfDualBicharacter_of_symm (V := Matrix α ν E) hψ hn h1 β hs hnd
  have hu : IsUnit b.det := isUnit_iff_ne_zero.mpr hd
  have hi : b⁻¹ * b = 1 := Matrix.nonsing_inv_mul b hu
  have hi' : b * b⁻¹ = 1 := Matrix.mul_nonsing_inv b hu
  have hbb : ∀ x y : Matrix α ν E, β (x * b) y = β x (y * b) := fun x y => by rw [hadj, hb]
  have hbi : ∀ x y : Matrix α ν E, β (x * b⁻¹) y = β x (y * b⁻¹) := fun x y => by
    have := hbb (x * b⁻¹) (y * b⁻¹)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.mul_one] at this
    exact this.symm
  have hpr : (pr c Q : Matrix α ν E → Matrix α ν E → F) = fun x y => β x y := by
    funext x y; exact (hβ x y).symm
  have hf : Continuous fun y : Matrix α ν E => ψ (2⁻¹ * β y (y * b)) := by
    have h2 : Continuous fun y : Matrix α ν E => (y, y * ((2⁻¹ : F) • b)) :=
      continuous_id.prodMk (continuous_id.matrix_mul continuous_const)
    have := hP.isLocallyConstant.continuous.comp h2
    refine this.congr fun y => ?_
    simp [Matrix.mul_smul]
  have hW := fun x => bicharacterFourier_mul_bicharacterFourier μ hP
    (f := fun y => ψ (2⁻¹ * β y (y * b)))
    (g := fun u => ψ (-(2⁻¹ * β (u * b⁻¹) u))) (s := fun u => u * b⁻¹) (γ := γ) hf
    (continuous_id.matrix_mul continuous_const) (fun y u => by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      have h3 : β (u * b⁻¹) (y * b) = β y u := by
        rw [← hbb, Matrix.mul_assoc, hi, Matrix.mul_one, hs]
      rw [Matrix.add_mul, Matrix.mul_assoc u, hi, Matrix.mul_one]
      simp only [map_add, LinearMap.add_apply, h3]
      ring) (by simpa only [hpr] using hG) hφ x
  funext x
  have hL : siegelParabolicOp c ψ χ Q (fromBlocks 1 b 0 1) (hermitianFourier c ψ Q μ φ) =
      fun y => ψ (2⁻¹ * β y (y * b)) * bicharacterFourier μ (fun x y => ψ (β x y)) φ y := by
    funext y
    simp [siegelParabolicOp, hermitianFourier, hsc, hpr]
  rw [hL]
  simp only [Pi.smul_apply, smul_eq_mul, hermitianFourier, hpr]
  rw [hW x]
  simp only [siegelParabolicOp, bicharacterFourier, hpr, toBlocks_fromBlocks₁₁,
      toBlocks_fromBlocks₁₂, det_one, hsc, Matrix.mul_one, one_mul]
  rw [mul_left_comm, ← integral_const_mul (ψ _)]
  congr 3
  funext z
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h4 : β (z * b⁻¹) x = β (x * b⁻¹) z := by rw [hbi, hs]
  simp only [Matrix.add_mul, Matrix.mul_neg, map_add, map_neg, LinearMap.add_apply,
      LinearMap.neg_apply, h4, ← hbi z z]
  ring



end Unitary.Internal

end Langlands.Theta
