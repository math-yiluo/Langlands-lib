import Langlands.Representation.Archimedean.JacquetKernel
import Langlands.Representation.Archimedean.RealJacquetSeparation
import Langlands.Representation.Archimedean.RealGenericParameterReduction
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Langlands.Representation.Archimedean.KIntegralInvariance

/-!
# Transposing an intertwiner of real standard modules inside an `O(n)`-matrix coefficient

Let `T` be a `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the real standard module of
`ds` to those of `ds'`, whose position characters are signed powers. For `v` in the `O(n)`-finite
principal series of the inverse characters of `ds'` there is `u` in that of the inverse
characters of `ds` with `∫ u h = ∫ v (T h)` over `O(n)` for all `h`
(`exists_pairing_transpose`; only the `O(n)`-equivariance of `T` is used,
`exists_pairing_transpose_of_rep`); then `∫ (T w)(κ g) v(κ) dκ = ∫ w(κ g) u(κ) dκ` for every
`g ∈ GL_n(ℝ)` (`integral_mul_transfer`): both sides agree on `O(n)`, have the same derivatives
and are real analytic along the `KAK` decomposition. Finally
`∫ w(κ g⁻¹) u(κ) dκ = ∫ u(κ g) w(κ) dκ` for `u`, `w` in principal series of inverse characters
(`integral_mul_inv_swap`).
-/

noncomputable section

open MeasureTheory Matrix ComplexConjugate

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff MonoidAlgebra

namespace Langlands.Archimedean

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace RealReverseTransfer

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet JacquetLimit JacquetDual
  GramFormula Langlands.GeneralLinear RealPrincipalSeriesDuality PrincipalSeriesExtension
  TranslateFinite JacquetKernel MatrixCoefficientAnalytic Langlands.LocalFactor.Archimedean

attribute [local instance] measurableSpaceK

local instance borelSpaceK_tr (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {n : ℕ}

/-! ## Generalities -/

/-- An equivariant linear map into the dual carries finite vectors to finite vectors of the
dual representation. -/
theorem isFiniteVector_dual_of_equivariant {K : Type*} [Group K] {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ K V}
    {σ : Representation ℂ K W} (L : W →ₗ[ℂ] Module.Dual ℂ V)
    (hL : ∀ (k : K) (w : W), L (σ k w) = ρ.dual k (L w)) {w : W}
    (hw : FiniteVectors.IsFiniteVector σ w) : FiniteVectors.IsFiniteVector ρ.dual (L w) := by
  have : FiniteDimensional ℂ (FiniteVectors.orbitSpan σ w) := hw
  change Module.Finite ℂ (FiniteVectors.orbitSpan ρ.dual (L w))
  refine Submodule.finiteDimensional_of_le (S₂ := (FiniteVectors.orbitSpan σ w).map L) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨σ k w, FiniteVectors.action_mem_orbitSpan σ k w, hL k w⟩

theorem toUnits_mk {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ : Matrix.unitaryGroup (Fin n) ℝ) = k :=
  Units.ext rfl

theorem mem_kFiniteFunctions_principalSeries {ds : List RealBlock}
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) :=
  ⟨realStandardModule_le_principalSeries n ds hf.1, hf.2⟩

/-- Right translation by `k ∈ O(n)` moves to the other factor of an `O(n)`-integral. -/
theorem integral_translate_mul (a b : Langlands.GeneralLinear n ℝ → ℂ)
    {k : Langlands.GeneralLinear n ℝ} (hk : k ∈ unitaryCompact ℝ n) :
    ∫ κ : unitaryCompact ℝ n, a ((κ : Langlands.GeneralLinear n ℝ) * k) *
        b (κ : Langlands.GeneralLinear n ℝ) ∂haarK n =
      ∫ κ : unitaryCompact ℝ n, a (κ : Langlands.GeneralLinear n ℝ) *
        b ((κ : Langlands.GeneralLinear n ℝ) * k⁻¹) ∂haarK n := by
  rw [← integral_mul_right_eq_self (μ := haarK n) (fun κ : unitaryCompact ℝ n =>
    a (κ : Langlands.GeneralLinear n ℝ) * b ((κ : Langlands.GeneralLinear n ℝ) * k⁻¹))
    (⟨k, hk⟩ : unitaryCompact ℝ n)]
  refine integral_congr_ae (ae_of_all _ fun κ => ?_)
  change a ((κ : Langlands.GeneralLinear n ℝ) * k) * b κ =
    a ((κ : Langlands.GeneralLinear n ℝ) * k) * b ((κ : Langlands.GeneralLinear n ℝ) * k * k⁻¹)
  rw [mul_inv_cancel_right]

/-! ## The integration pairing -/

/-- The pairing `⟨a, b⟩ = ∫_{O(n)} a(k) b(k) dk` of two spaces of continuous functions. -/
def intPairing (A B : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hA : ∀ a ∈ A, Continuous a) (hB : ∀ b ∈ B, Continuous b) : A →ₗ[ℂ] B →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun a b => ∫ k, (a : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) *
      (b : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) ∂haarK n)
    (fun a₁ a₂ b => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_mul_of_continuous (hA _ a₁.2) (hB _ b.2))
        (integrable_mul_of_continuous (hA _ a₂.2) (hB _ b.2)))
    (fun c a b => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun a b₁ b₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_of_continuous (hA _ a.2) (hB _ b₁.2))
        (integrable_mul_of_continuous (hA _ a.2) (hB _ b₂.2)))
    (fun c a b => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem intPairing_apply (A B : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
    (hA : ∀ a ∈ A, Continuous a) (hB : ∀ b ∈ B, Continuous b) (a : A) (b : B) :
    intPairing A B hA hB a b =
      ∫ k, (a : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) *
        (b : Langlands.GeneralLinear n ℝ → ℂ) (k : Langlands.GeneralLinear n ℝ) ∂haarK n :=
  rfl

/-! ## Separation -/

/-- **Separation by the dual principal series.** A nonzero `O(n)`-finite function `h` of the
principal series of signed-power characters `χ` pairs nontrivially with some `O(n)`-finite
function of the principal series of `χ⁻¹`: the extension of `conj(h)` from `O(n)`. -/
theorem exists_integral_mul_ne_zero {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e)
    {h : Langlands.GeneralLinear n ℝ → ℂ}
    (hh : h ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) (h0 : h ≠ 0) :
    ∃ u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n),
      ∫ k, u (k : Langlands.GeneralLinear n ℝ) * h k ∂haarK n ≠ 0 := by
  obtain ⟨g, hg⟩ : ∃ g, h g ≠ 0 := Function.ne_iff.mp h0
  obtain ⟨k₀, hk₀⟩ := exists_mem_unitaryCompact_ne_zero hh.1 hg
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    (continuous_of_mem hh) hh.2 1
  set φ : Matrix.unitaryGroup (Fin n) ℝ → ℂ := fun κ => conj (h (Unitary.toUnits κ)) with hφdef
  have hφP : ∀ κ : Matrix.unitaryGroup (Fin n) ℝ, φ κ = MvPolynomial.eval
      (fun ij => (((κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
    intro κ
    rw [hφdef]
    simp only
    rw [← one_mul (Unitary.toUnits κ), hP κ]
    exact conj_eval_ofReal P (fun ij => (κ : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2)
  have hφc : Continuous φ :=
    Complex.continuous_conj.comp ((continuous_of_mem hh).comp continuous_unitary_toUnits)
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k))) := by
    have h' := finiteDimensional_span_eval (n := n) (MvPolynomial.map (starRingEnd ℂ) P)
    have heq : (fun k : Matrix.unitaryGroup (Fin n) ℝ => fun x => φ (x * k)) =
        fun k x => MvPolynomial.eval (fun ij => (((x * k : Matrix.unitaryGroup (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℂ)) (MvPolynomial.map (starRingEnd ℂ) P) :=
      funext fun k => funext fun x => hφP (x * k)
    rw [heq]
    exact h'
  have hφM : ∀ (a : Fin n → ℝˣ) (κ : Matrix.unitaryGroup (Fin n) ℝ),
      φ (signDiagonal (fun i => (a i : ℝ)) * κ) =
        principalSeriesCharacter ℝ n (dualChar χ) (fun i => signUnit (a i)) * φ κ := by
    intro a κ
    simp only [hφdef]
    rw [signDiagonal_toUnits, hh.1.2, map_mul, principalSeriesCharacter_sign,
      principalSeriesCharacter_sign, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dualChar, conj_eq_inv_of_norm_eq_one (hχ.norm_sign i (a i))]
  have hE := extension_mem_kFiniteFunctions (fun l => -e l) hχ.dual.eq hφc hfin hφM
  set u := extension (shiftedExponent n (fun l => -e l)) φ with hudef
  have hu_val : ∀ k : unitaryCompact ℝ n, u k = conj (h k) := by
    intro k
    have hk : (k : Langlands.GeneralLinear n ℝ) = Unitary.toUnits (toUnitaryGroup n k) :=
      Units.ext rfl
    rw [hudef, hk, extension_unitary, hφdef]
  refine ⟨u, hE, ?_⟩
  have hint : (fun k : unitaryCompact ℝ n => u (k : Langlands.GeneralLinear n ℝ) *
      h (k : Langlands.GeneralLinear n ℝ)) =
      fun k : unitaryCompact ℝ n => ((‖h (k : Langlands.GeneralLinear n ℝ)‖ ^ 2 : ℝ) : ℂ) := by
    funext k
    rw [hu_val, Complex.conj_mul', Complex.ofReal_pow]
  rw [hint, integral_complex_ofReal, Complex.ofReal_ne_zero]
  have hc : Continuous fun k : unitaryCompact ℝ n => ‖h (k : Langlands.GeneralLinear n ℝ)‖ ^ 2 :=
    ((continuous_comp_val (continuous_of_mem hh)).norm).pow 2
  refine (hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := k₀)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) ?_).ne'
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hk₀)

/-! ## The pairing transpose -/

/-- **The pairing transpose.** Let `T` be a linear map from the `O(n)`-finite functions of the
real standard module of `ds` (signed-power position characters `χ`) to those of `ds'`
(characters `ψ`) that commutes with `O(n)`. For every `O(n)`-finite `v` in the principal series
of `ψ⁻¹` there is an `O(n)`-finite `u` in the principal series of `χ⁻¹` with
`∫ u h = ∫ v (T h)` for all `h`. -/
theorem exists_pairing_transpose_of_rep {ds ds' : List RealBlock} {e : ℕ → ℂ}
    (hχ : IsSignedPower (realPositionCharacter ds) e)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (hTK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ)
      (h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)),
      T (realStandardRep n ds k h) = realStandardRep n ds' k (T h))
    {v : Langlands.GeneralLinear n ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds')))
      (unitaryCompact ℝ n)) :
    ∃ u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n),
      ∀ h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
        ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) * (h : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n =
          ∫ κ, v (κ : Langlands.GeneralLinear n ℝ) * (T h : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n := by
  set χ := realPositionCharacter ds with hχdef
  set D := kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) with hD
  set D' := kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds')))
    (unitaryCompact ℝ n) with hD'
  let S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
  let S' := kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n)
  have hDc : ∀ a ∈ D, Continuous a := fun a ha => continuous_of_mem ha
  have hD'c : ∀ a ∈ D', Continuous a := fun a ha => continuous_of_mem ha
  have hSc : ∀ a ∈ S, Continuous a := fun a ha => continuous_of_mem_kFiniteFunctions ha
  have hS'c : ∀ a ∈ S', Continuous a := fun a ha => continuous_of_mem_kFiniteFunctions ha
  let Qd : D →ₗ[ℂ] Module.Dual ℂ S := intPairing D S hDc hSc
  let Λ : D' →ₗ[ℂ] Module.Dual ℂ S := (intPairing D' S' hD'c hS'c).compl₂ T
  have hQdK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (u : D),
      Qd (principalSeriesRep ℝ n (dualChar χ) k u) = (realStandardRep n ds).dual k (Qd u) := by
    intro k u
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply]
    change intPairing D S hDc hSc _ h = intPairing D S hDc hSc u _
    rw [intPairing_apply, intPairing_apply, principalSeriesRep_apply_coe,
      realStandardRep_apply_coe, map_inv]
    exact integral_translate_mul _ _ k.2
  have hΛK : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (w : D'),
      Λ (principalSeriesRep ℝ n (dualChar (realPositionCharacter ds')) k w) =
        (realStandardRep n ds).dual k (Λ w) := by
    intro k w
    refine LinearMap.ext fun h => ?_
    rw [KFiniteDual.dual_apply_apply]
    change intPairing D' S' hD'c hS'c _ (T h) = intPairing D' S' hD'c hS'c w (T _)
    rw [intPairing_apply, intPairing_apply, principalSeriesRep_apply_coe, hTK,
      realStandardRep_apply_coe, map_inv]
    exact integral_translate_mul _ _ k.2
  have hgk := isRealGKModule_realStandardModule n ds
  have : IsSemisimpleModule ℂ[Matrix.unitaryGroup (Fin n) ℝ] (realStandardRep n ds).asModule :=
    KFiniteDual.isSemisimpleModule hgk.1 hgk.2.1
  have hblock := KFiniteDual.finiteDimensional_block hgk.1 hgk.2.1 (realStandardAdmissible n ds)
  let W' : Subrepresentation (realStandardRep n ds).dual :=
    { toSubmodule := LinearMap.range Qd
      apply_mem_toSubmodule := by
        rintro k _ ⟨g, rfl⟩
        exact ⟨principalSeriesRep ℝ n (dualChar χ) k g, hQdK k g⟩ }
  have hW' : ∀ w ∈ W', FiniteVectors.IsFiniteVector (realStandardRep n ds).dual w := by
    rintro _ ⟨g, rfl⟩
    exact isFiniteVector_dual_of_equivariant Qd hQdK
      ((isRealGKModule_principalSeries n (dualChar χ)).1 g)
  have hsep : ∀ h : S, (∀ w ∈ W', w h = 0) → h = 0 := by
    intro h hh
    by_contra hne
    have hne' : (h : Langlands.GeneralLinear n ℝ → ℂ) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    obtain ⟨u, hu, hu0⟩ := exists_integral_mul_ne_zero hχ
      (mem_kFiniteFunctions_principalSeries h.2) hne'
    exact hu0 (hh _ ⟨⟨u, hu⟩, rfl⟩)
  obtain ⟨u, hu⟩ := KFiniteDual.mem_of_separating hblock W' hW' hsep
    (isFiniteVector_dual_of_equivariant Λ hΛK
      ((isRealGKModule_principalSeries n (dualChar (realPositionCharacter ds'))).1 ⟨v, hv⟩))
  exact ⟨u, u.2, fun h => congrArg (fun ℓ => ℓ h) hu⟩

/-- **The pairing transpose of an intertwiner.** `exists_pairing_transpose_of_rep` for a
`(𝔤, K)`-intertwiner `T`. -/
theorem exists_pairing_transpose {ds ds' : List RealBlock} {e : ℕ → ℂ}
    (hχ : IsSignedPower (realPositionCharacter ds) e)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (hT : IsRealStandardIntertwiner n (realStandardRep n ds') (realStandardLie n ds') ds T)
    {v : Langlands.GeneralLinear n ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds')))
      (unitaryCompact ℝ n)) :
    ∃ u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n),
      ∀ h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
        ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) * (h : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n =
          ∫ κ, v (κ : Langlands.GeneralLinear n ℝ) * (T h : Langlands.GeneralLinear n ℝ → ℂ) κ
            ∂haarK n :=
  exists_pairing_transpose_of_rep hχ T hT.map_realStandardRep hv

/-- `∫ w(κ g⁻¹) u(κ) dκ = ∫ u(κ g) w(κ) dκ` for `u`, `w` in the principal series of `χ⁻¹`
and `χ` (invariance of the `O(n)`-integral of modulus-equivariant functions). -/
theorem integral_mul_inv_swap {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ} (hχ : IsSignedPower χ e)
    {u w : Langlands.GeneralLinear n ℝ → ℂ} (hu : u ∈ principalSeries ℝ n (dualChar χ))
    (hw : w ∈ principalSeries ℝ n χ) (g : Langlands.GeneralLinear n ℝ) :
    ∫ κ, w ((κ : Langlands.GeneralLinear n ℝ) * g⁻¹) * u κ ∂haarK n =
      ∫ κ, u ((κ : Langlands.GeneralLinear n ℝ) * g) * w κ ∂haarK n := by
  have hug := rightTranslation_mem_principalSeries (dualChar χ) hu g
  have h := kIntegralInvariance n
    (fun x => Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) g u x * w x)
    (contMDiff_mul_fun hug.1 hw.1)
    (isModulusEquivariant_mul (fun i x => inv_mul_cancel₀ (hχ.ne_zero i x)) hug hw) g⁻¹
  simp only [TranslateFinite.rightTranslation_apply, inv_mul_cancel_right] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)

/-! ## Equality of matrix coefficients from equality at `1` -/

section Pairs

variable (μ : Measure (Matrix.unitaryGroup (Fin n) ℝ)) [IsFiniteMeasure μ]

/-- **Equality of two families of matrix coefficients.** Let `P` be a relation between
`O(n)`-finite functions of the principal series of `χ₁` and of `χ₂`, stable under right
translation by `O(n)` and under all right derivatives applied to both sides. If the matrix
coefficients against `φ₁`, `φ₂` of related functions agree at `1`, they agree everywhere. -/
theorem matrixCoefficient_eq_of_rel {χ₁ χ₂ : ℕ → ℝˣ → ℂ} (e₁ e₂ : ℕ → ℂ)
    (hχ₁ : ∀ (l : ℕ) (x : ℝˣ), χ₁ l x = χ₁ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e₁ l)
    (hχ₂ : ∀ (l : ℕ) (x : ℝˣ), χ₂ l x = χ₂ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e₂ l)
    (P : (Langlands.GeneralLinear n ℝ → ℂ) → (Langlands.GeneralLinear n ℝ → ℂ) → Prop)
    (hP : ∀ a b, P a b → a ∈ kFiniteFunctions (principalSeries ℝ n χ₁) (unitaryCompact ℝ n) ∧
      b ∈ kFiniteFunctions (principalSeries ℝ n χ₂) (unitaryCompact ℝ n))
    (hPK : ∀ k ∈ unitaryCompact ℝ n, ∀ a b, P a b →
      P (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k a)
        (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k b))
    (hPD : ∀ (X : Matrix (Fin n) (Fin n) ℝ) a b, P a b →
      P (rightDerivative (matrixModel ℝ n) X a) (rightDerivative (matrixModel ℝ n) X b))
    {φ₁ φ₂ : Matrix.unitaryGroup (Fin n) ℝ → ℂ} (hφ₁ : Continuous φ₁) (hφ₂ : Continuous φ₂)
    (h1 : ∀ a b, P a b → MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ 1 =
      MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ 1) :
    ∀ a b, P a b → ∀ g, MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ g =
      MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ g := by
  -- along a diagonal one-parameter subgroup
  have hexp : ∀ (h : Fin n → ℝ) (g : Langlands.GeneralLinear n ℝ),
      (∀ a b, P a b → MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ g =
        MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ g) →
      ∀ a b, P a b → ∀ t : ℝ,
        MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiagonal h t) =
          MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiagonal h t) := by
    intro h g h0 a b hab t
    have hderiv : ∀ a b, P a b →
        deriv (fun t => MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiagonal h t) -
          MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiagonal h t)) =
        fun t => MatrixCoefficientAnalytic.matrixCoefficient μ
            (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) a) φ₁ (g * expDiagonal h t) -
          MatrixCoefficientAnalytic.matrixCoefficient μ
            (rightDerivative (matrixModel ℝ n) (Matrix.diagonal h) b) φ₂
            (g * expDiagonal h t) := fun a b hab => funext fun t =>
      ((analyticAt_matrixCoefficient μ e₁ hχ₁ (hP a b hab).1 hφ₁ g h t).2.sub
        (analyticAt_matrixCoefficient μ e₂ hχ₂ (hP a b hab).2 hφ₂ g h t).2).deriv
    have hiter : ∀ j : ℕ, ∀ a b, P a b →
        iteratedDeriv j (fun t =>
          MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ (g * expDiagonal h t) -
            MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ (g * expDiagonal h t)) 0 = 0 := by
      intro j
      induction j with
      | zero =>
        intro a b hab
        rw [iteratedDeriv_zero]
        simp only [expDiagonal_zero, mul_one]
        rw [h0 a b hab, sub_self]
      | succ j ih =>
        intro a b hab
        rw [iteratedDeriv_succ', hderiv a b hab]
        exact ih _ _ (hPD _ a b hab)
    have := eq_zero_of_iteratedDeriv_eq_zero
      (fun t _ => (analyticAt_matrixCoefficient μ e₁ hχ₁ (hP a b hab).1 hφ₁ g h t).1.sub
        (analyticAt_matrixCoefficient μ e₂ hχ₂ (hP a b hab).2 hφ₂ g h t).1)
      (hiter · a b hab)
    exact sub_eq_zero.mp (congrFun this t)
  intro a b hab g
  obtain ⟨k₁, hk₁, k₂, hk₂, h, rfl⟩ := exists_kak g
  rw [matrixCoefficient_mul_unitary μ a φ₁ (k₁ * expDiagonal h 1) k₂,
    matrixCoefficient_mul_unitary μ b φ₂ (k₁ * expDiagonal h 1) k₂]
  have hk1 : ∀ a b, P a b → MatrixCoefficientAnalytic.matrixCoefficient μ a φ₁ k₁ =
      MatrixCoefficientAnalytic.matrixCoefficient μ b φ₂ k₁ :=
    fun a b hab => by
      have e1 := matrixCoefficient_mul_unitary μ a φ₁ 1 k₁
      have e2 := matrixCoefficient_mul_unitary μ b φ₂ 1 k₁
      rw [one_mul] at e1 e2
      rw [e1, e2]
      exact h1 _ _ (hPK k₁ hk₁ a b hab)
  exact hexp h k₁ hk1 _ _ (hPK k₂ hk₂ a b hab) 1

end Pairs

/-! ## The transfer identity -/

/-- **The transfer identity.** Let `T` be an intertwiner from the `O(n)`-finite functions of the
real standard module of `ds` to those of `ds'` (position characters `χ`, `ψ`, signed powers),
`v` an `O(n)`-finite function of the principal series of `ψ⁻¹` and `u` one of `χ⁻¹` with
`∫ u h = ∫ v (T h)` for all `h`. Then `∫ (T w)(κ g) v(κ) dκ = ∫ w(κ g) u(κ) dκ` for every `w`
and every `g ∈ GL_n(ℝ)`. -/
theorem integral_mul_transfer {ds ds' : List RealBlock} {e e' : ℕ → ℂ}
    (hχ : IsSignedPower (realPositionCharacter ds) e)
    (hψ : IsSignedPower (realPositionCharacter ds') e')
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds') (unitaryCompact ℝ n))
    (hT : IsRealStandardIntertwiner n (realStandardRep n ds') (realStandardLie n ds') ds T)
    {u v : Langlands.GeneralLinear n ℝ → ℂ}
    (hv : v ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds')))
      (unitaryCompact ℝ n))
    (hu : u ∈ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ n))
    (huv : ∀ h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n),
      ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) * (h : Langlands.GeneralLinear n ℝ → ℂ) κ
          ∂haarK n =
        ∫ κ, v (κ : Langlands.GeneralLinear n ℝ) * (T h : Langlands.GeneralLinear n ℝ → ℂ) κ
          ∂haarK n)
    (w : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))
    (g : Langlands.GeneralLinear n ℝ) :
    ∫ κ, (T w : Langlands.GeneralLinear n ℝ → ℂ) ((κ : Langlands.GeneralLinear n ℝ) * g) *
        v κ ∂haarK n =
      ∫ κ, (w : Langlands.GeneralLinear n ℝ → ℂ) ((κ : Langlands.GeneralLinear n ℝ) * g) *
        u κ ∂haarK n := by
  set μ := (haarK n).map (toUnitaryGroup n)
  let S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
  set P : (Langlands.GeneralLinear n ℝ → ℂ) → (Langlands.GeneralLinear n ℝ → ℂ) → Prop :=
    fun a b => ∃ w' : S,
      a = (T w' : Langlands.GeneralLinear n ℝ → ℂ) ∧ b = (w' : Langlands.GeneralLinear n ℝ → ℂ)
    with hPdef
  have hvc := continuous_of_mem hv
  have huc := continuous_of_mem hu
  have hcont : ∀ {a b : Langlands.GeneralLinear n ℝ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℝ,
        Continuous fun y : Langlands.GeneralLinear n ℝ => a (y * g) * b y :=
    fun ha hb g => (ha.comp (continuous_id.mul continuous_const)).mul hb
  have hmc : ∀ {a b : Langlands.GeneralLinear n ℝ → ℂ}, Continuous a → Continuous b →
      ∀ g : Langlands.GeneralLinear n ℝ,
        MatrixCoefficientAnalytic.matrixCoefficient μ a (b ∘ Unitary.toUnits) g =
          ∫ κ, a ((κ : Langlands.GeneralLinear n ℝ) * g) * b κ ∂haarK n := by
    intro a b ha hb g
    simp only [MatrixCoefficientAnalytic.matrixCoefficient]
    exact integral_map_toUnitaryGroup (f := fun y => a (y * g) * b y) (hcont ha hb g)
  have key := matrixCoefficient_eq_of_rel μ e' e hψ.eq hχ.eq P
    (fun a b ⟨w', ha, hb⟩ => ⟨ha ▸ mem_kFiniteFunctions_principalSeries (T w').2,
      hb ▸ mem_kFiniteFunctions_principalSeries w'.2⟩)
    (fun k hk a b ⟨w', ha, hb⟩ => by
      refine ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w', ?_, ?_⟩
      · rw [hT.map_realStandardRep, realStandardRep_apply_coe, toUnits_mk, ha]
      · rw [realStandardRep_apply_coe, toUnits_mk, hb])
    (fun X a b ⟨w', ha, hb⟩ => by
      refine ⟨realStandardLie n ds (1 ⊗ₜ X) w', ?_, ?_⟩
      · rw [hT.map_realStandardLie, realStandardLie_one_tmul_apply_coe, ha]
      · rw [realStandardLie_one_tmul_apply_coe, hb])
    (hvc.comp continuous_unitary_toUnits) (huc.comp continuous_unitary_toUnits)
    (fun a b ⟨w', ha, hb⟩ => by
      subst ha hb
      rw [hmc (continuous_of_mem_kFiniteFunctions (T w').2) hvc,
        hmc (continuous_of_mem_kFiniteFunctions w'.2) huc]
      simp only [mul_one]
      have e := huv w'
      calc ∫ κ, (T w' : Langlands.GeneralLinear n ℝ → ℂ) (κ : Langlands.GeneralLinear n ℝ) *
              v κ ∂haarK n
          = ∫ κ, v (κ : Langlands.GeneralLinear n ℝ) *
              (T w' : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n :=
            integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)
        _ = ∫ κ, u (κ : Langlands.GeneralLinear n ℝ) *
              (w' : Langlands.GeneralLinear n ℝ → ℂ) κ ∂haarK n := e.symm
        _ = _ := integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _))
    _ _ ⟨w, rfl, rfl⟩ g
  rwa [hmc (continuous_of_mem_kFiniteFunctions (T w).2) hvc,
    hmc (continuous_of_mem_kFiniteFunctions w.2) huc] at key

end RealReverseTransfer

end Langlands.Archimedean
