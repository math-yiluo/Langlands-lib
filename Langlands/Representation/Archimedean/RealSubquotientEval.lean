import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesInfinitesimalCharacter
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof

/-!
# Principal series of `GL_n(ℝ)` evaluated at the identity

Helper results for Harish-Chandra's subquotient theorem (`RealPrincipalSeriesSubquotientStatement`).

* `rightDerivative_upper_apply_one`: for `f` in the principal series of the characters
  `chars a e` and `U` upper triangular, `(R(U) f)(1) = (∑ⱼ aⱼ Uⱼⱼ) f(1)`.
* `IsTypeDerivative`: `D` is the derivative of a matrix representation `τ` of `O(n)` along curves
  through `1`; `apply_skew_intertwiner`: a `K`-intertwiner `T` from `τ` to a
  `(𝔤𝔩_n(ℝ), O(n))`-module satisfies `π(1 ⊗ Y) (T x) = T (D(Y) x)` for antisymmetric `Y`.
* `exists_frobenius_intertwiner`: every functional `φ` on `ℂ^d` on which the sign matrices act by
  the signs `e` is `x ↦ (T x)(1)` for a `K`-intertwiner `T` from `τ` to the `O(n)`-finite
  principal series of `chars a e` (Frobenius reciprocity, through `RealJacquetFrobenius.frobFun`).
* `eq_zero_of_signFunctional`: the sign functionals separate the points of `ℂ^d`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

namespace RealSubquotient

open Langlands.LocalFactor.Archimedean RealJacquetFrobenius

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-- The list of blocks of the principal series of the characters `chars a e`. -/
abbrev psList (a : Fin n → ℂ) (e : Fin n → Fin 2) : List RealBlock :=
  (List.ofFn (chars a e)).map RealBlock.character

/-- The `O(n)`-finite functions of the principal series of the characters `chars a e`. -/
abbrev PS (a : Fin n → ℂ) (e : Fin n → Fin 2) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  kFiniteFunctions (realStandardModule n (psList a e)) (unitaryCompact ℝ n)

/-! ## Upper triangular derivatives at the identity -/

/-- For `f` in the principal series of the characters `chars a e` and `U` upper triangular,
`(R(U) f)(1) = (∑ⱼ aⱼ Uⱼⱼ) f(1)`: along the curve `exp(t diag U) (1 + t N)` the function is
`exp(t ∑ⱼ aⱼ Uⱼⱼ) f(1)`. -/
theorem rightDerivative_upper_apply_one {a : Fin n → ℂ} {e : Fin n → Fin 2}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n (posChar a e))
    {U : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsUpperTriangular) :
    rightDerivative (matrixModel ℝ n) U f 1 = (∑ j, a j * (U j j : ℂ)) * f 1 := by
  rw [rightDerivative_eq_fderiv hf.1, Units.val_one, one_mul]
  set s : ℂ := ∑ j, a j * (U j j : ℂ) with hs
  set Δ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal fun i => U i i with hΔ
  set N : Matrix (Fin n) (Fin n) ℝ := U - Δ with hN
  have hNu : N.IsUpperTriangular := hU.sub (Matrix.blockTriangular_diagonal _)
  have hNd : ∀ i, N i i = 0 := fun i => by simp [hN, hΔ]
  set Γ : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t =>
    NormedSpace.exp (t • Δ) * (1 + t • N) with hΓ
  have hΓd : HasDerivAt Γ U 0 := by
    have h1 := RealPrincipalSeriesDuality.hasDerivAt_exp_smul_zero Δ
    have h2 : HasDerivAt (fun t : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + t • N) N 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add 1
    refine (h1.mul h2).congr_deriv ?_
    simp only [zero_smul, add_zero, NormedSpace.exp_zero, one_mul, mul_one]
    rw [hN, add_sub_cancel]
  have hΓ0 : Γ 0 = 1 := by simp [hΓ]
  have hval : ∀ t : ℝ, Γ t = ((matrixExpUnit n (Matrix.diagonal fun i => t * U i i) *
      ((RealPrincipalSeriesDuality.unipotentLine N hNu hNd t :
        Langlands.GeneralLinear.upperUnipotent n ℝ) : Langlands.GeneralLinear n ℝ) * 1 :
      Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    intro t
    have hsd : t • Δ = Matrix.diagonal fun i => t * U i i := by
      rw [hΔ, ← Matrix.diagonal_smul]
      rfl
    simp only [Units.val_mul, matrixExpUnit_val, RealPrincipalSeriesDuality.unipotentLine_val,
      hΓ, hsd, mul_one]
  have hcomp : (fun t => unitsExtension f (Γ t)) =
      fun t : ℝ => Complex.exp ((t : ℂ) * s) * f 1 := by
    funext t
    rw [hval t, unitsExtension_val, RealPrincipalSeriesDuality.matrixExpUnit_diagonal,
      ((mem_principalSeries_iff ℝ n _ f).mp hf).2, principalSeriesCharacter_eq]
    congr 1
    unfold diagChar
    rw [hs, Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Matrix.diagonal_apply_eq, Units.val_mk0, charFun_exp]
    congr 1
    push_cast
    ring
  have hd1 : HasDerivAt (fun t => unitsExtension f (Γ t))
      (fderiv ℝ (unitsExtension f) (1 : Matrix (Fin n) (Fin n) ℝ) U) 0 := by
    have hdiff : HasFDerivAt (unitsExtension f)
        (fderiv ℝ (unitsExtension f) (1 : Matrix (Fin n) (Fin n) ℝ)) (Γ 0) := by
      rw [hΓ0]
      have h := differentiableAt_unitsExtension hf.1 (Units.isUnit (1 : Langlands.GeneralLinear n ℝ))
      rw [Units.val_one] at h
      exact h.hasFDerivAt
    exact hdiff.comp_hasDerivAt (0 : ℝ) hΓd
  have hd2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * s) * f 1) (s * f 1) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const s).cexp).mul_const (f 1)
    simpa using this
  rw [hcomp] at hd1
  exact hd1.unique hd2

/-! ## Derivatives of `K`-types -/

/-- `D` is the derivative of the matrix representation `τ` of `O(n)`: along every curve `γ` in
`O(n)` with `γ(0) = 1` whose entries have derivative `X` at `0`, the entries of `τ(γ(t))` have
derivative `D(X)` at `0`. -/
def IsTypeDerivative {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ), γ 0 = 1 →
    (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j) (X i j) 0) →
      ∀ i j, HasDerivAt (fun t => τ (γ t) i j) (D X i j) 0

/-- A linear functional of `M *ᵥ x` along a curve of matrices with differentiable entries. -/
theorem hasDerivAt_apply_mulVec {d : ℕ} {M : ℝ → Matrix (Fin d) (Fin d) ℂ}
    {M' : Matrix (Fin d) (Fin d) ℂ} (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) 0)
    (g : (Fin d → ℂ) →ₗ[ℂ] ℂ) (x : Fin d → ℂ) :
    HasDerivAt (fun t => g (M t *ᵥ x)) (g (M' *ᵥ x)) 0 := by
  have hexp : ∀ N : Matrix (Fin d) (Fin d) ℂ, g (N *ᵥ x) =
      ∑ i, ∑ j, N i j * x j * g (fun k => if i = k then 1 else 0) := by
    intro N
    rw [LinearMap.pi_apply_eq_sum_univ g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]
  simp only [hexp]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact ((hM i j).mul_const (x j)).mul_const _

/-- A `K`-intertwiner `T` from `τ` into a `(𝔤𝔩_n(ℝ), O(n))`-module satisfies
`π(1 ⊗ Y)(T x) = T(D(Y) x)` for antisymmetric `Y`: differentiate `t ↦ ℓ(ρ(exp(tY)) T x) =
ℓ(T(τ(exp(tY)) x))` at `0`. -/
theorem apply_skew_intertwiner {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} (hgk : IsRealGKModule n ρ π)
    {d : ℕ} {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ}
    {D : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ} (hD : IsTypeDerivative τ D)
    {T : (Fin d → ℂ) →ₗ[ℂ] V} (hT : T ∈ gkIntertwiners ρ d τ)
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Yᵀ = -Y) (x : Fin d → ℂ) :
    π (1 ⊗ₜ Y) (T x) = T (D Y *ᵥ x) := by
  set γ := RealJacquetFiniteGeneration.skewCurve Y hY
  have h0 : γ 0 = 1 := by
    apply Subtype.ext
    simp [γ, RealJacquetFiniteGeneration.skewCurve]
  have hentry : ∀ i j, HasDerivAt
      (fun t => (γ t : Matrix (Fin n) (Fin n) ℝ) i j) (Y i j) 0 :=
    fun i j => RealJacquetFiniteGeneration.skew_hasDerivAt_entry
      (RealJacquetFiniteGeneration.skew_hasDerivAt_exp_smul_zero Y) i j
  rw [← sub_eq_zero]
  refine (_root_.Module.forall_dual_apply_eq_zero_iff ℂ
    (π (1 ⊗ₜ Y) (T x) - T (D Y *ᵥ x))).mp fun ℓ => ?_
  have h1 := hgk.2.2.1 γ Y h0 hentry (T x) ℓ
  have h2 := hasDerivAt_apply_mulVec (hD γ Y h0 hentry) (ℓ ∘ₗ T) x
  have h3 : (fun t => ℓ (ρ (γ t) (T x))) = fun t => (ℓ ∘ₗ T) (τ (γ t) *ᵥ x) := by
    funext t
    rw [LinearMap.comp_apply, hT (γ t) x]
  rw [h3] at h1
  rw [map_sub, h1.unique h2, LinearMap.comp_apply, sub_self]

/-! ## Frobenius reciprocity for `K`-types -/

/-- A linear functional on `ℂ^d` evaluated at `N *ᵥ x`, expanded in coordinates. -/
theorem apply_mulVec_eq_sum {d : ℕ} (g : (Fin d → ℂ) →ₗ[ℂ] ℂ) (N : Matrix (Fin d) (Fin d) ℂ)
    (x : Fin d → ℂ) :
    g (N *ᵥ x) = ∑ i, ∑ j, N i j * x j * g (fun k => if i = k then 1 else 0) := by
  rw [LinearMap.pi_apply_eq_sum_univ g]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, Matrix.mulVec, dotProduct, Finset.sum_mul]

/-- The representation of `O(n)` on `ℂ^d` by the matrices `τ(k)`. -/
def matRep {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) (Fin d → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toRingEquiv.toMonoidHom.comp τ

theorem matRep_apply {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℝ) (x : Fin d → ℂ) : matRep τ k x = τ k *ᵥ x :=
  rfl

/-- `φ` is a sign functional with signs `e`: the sign matrix `s_j` acts on it by `(-1)^{e_j}`. -/
def IsSignFunctional {d : ℕ} (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (e : Fin n → Fin 2) (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (j : Fin n) (x : Fin d → ℂ), φ (τ (signReflection n j) *ᵥ x) = (-1) ^ (e j).val * φ x

/-- **Frobenius reciprocity.** For continuous `τ` and a sign functional `φ` with signs `e`, there
is a `K`-intertwiner `T` from `τ` into the `O(n)`-finite principal series of `chars a e` with
`(T x)(1) = φ x`: the Frobenius function `T x (b k) = χ(b) φ(τ(k) x)`. -/
theorem exists_frobenius_intertwiner {d : ℕ}
    {τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ} (hτ : Continuous τ)
    (a : Fin n → ℂ) (e : Fin n → Fin 2) {φ : (Fin d → ℂ) →ₗ[ℂ] ℂ}
    (hφ : IsSignFunctional τ e φ) :
    ∃ T ∈ gkIntertwiners (realStandardRep n (psList a e)) d τ,
      ∀ x, ((T x : PS a e) : Langlands.GeneralLinear n ℝ → ℂ) 1 = φ x := by
  have hsign : ∀ (j : Fin n) (v : Fin d → ℂ),
      φ (matRep τ (signReflection n j) v) = (-1) ^ (e j).val * φ v := fun j v => hφ j v
  have hfin : ∀ v : Fin d → ℂ, FiniteVectors.IsFiniteVector (matRep τ) v := fun v => by
    unfold FiniteVectors.IsFiniteVector
    infer_instance
  have hcont : ∀ (v : Fin d → ℂ) (ℓ' : (Fin d → ℂ) →ₗ[ℂ] ℂ),
      Continuous fun k : Matrix.unitaryGroup (Fin n) ℝ => ℓ' (matRep τ k v) := by
    intro v ℓ'
    simp only [matRep_apply, apply_mulVec_eq_sum]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((hτ.matrix_elem i j).mul continuous_const).mul continuous_const
  have hmem : ∀ v : Fin d → ℂ, frobLin (matRep τ) φ a e v ∈ PS a e := by
    intro v
    refine Submodule.mem_inf.mpr ⟨⟨(mem_principalSeries_iff ℝ n _ _).mpr
      ⟨contMDiff_frobFun hsign hfin hcont v, frobFun_left hsign v⟩, ?_⟩,
      frobFun_mem_kFiniteVectors hsign v (hfin v)⟩
    intro p d hd
    rw [RealPrincipalSeriesDuality.realInducedBlockAt_map_character] at hd
    exact absurd hd (by simp)
  refine ⟨(frobLin (matRep τ) φ a e).codRestrict _ hmem, ?_, ?_⟩
  · intro k x
    apply Subtype.ext
    let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits k, k.2⟩
    have hk : (⟨((k' : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k'.2⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = k := Subtype.ext rfl
    have h := frobFun_rightTranslation (a := a) hsign k' x
    rw [hk, matRep_apply] at h
    rw [realStandardRep_apply_coe]
    exact h
  · intro x
    change frobFun (matRep τ) φ a e x 1 = φ x
    rw [frobFun_eq (b := 1) (k := 1) hsign Matrix.blockTriangular_one (one_mem _) (by simp) x,
      diagChar_one, one_mul]
    change φ (matRep τ 1 x) = φ x
    rw [map_one, Module.End.one_apply]

/-! ## Sign functionals separate points -/

/-- The sign matrices `τ(s_j)` square to `1` and commute. -/
theorem signReflection_mul_self (j : Fin n) : signReflection n j * signReflection n j = 1 := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = (1 : Matrix (Fin n) (Fin n) ℝ)
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = j <;> simp [h]

theorem signReflection_comm (i j : Fin n) :
    signReflection n i * signReflection n j = signReflection n j * signReflection n i := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  ring

/-- Every linear functional on `ℂ^d` is a sum of sign functionals. -/
theorem mem_span_signFunctional {d : ℕ}
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ) :
    φ ∈ Submodule.span ℂ {ψ | ∃ e : Fin n → Fin 2, IsSignFunctional τ e ψ} := by
  classical
  set s : Fin n → Matrix (Fin d) (Fin d) ℂ := fun j => τ (signReflection n j) with hs
  have hss : ∀ j, s j * s j = 1 := fun j => by
    rw [hs, ← map_mul, signReflection_mul_self, map_one]
  have hcomm : ∀ i j, s i * s j = s j * s i := fun i j => by
    rw [hs, ← map_mul, ← map_mul, signReflection_comm]
  -- `cond j ψ`: `s_j` acts on `ψ` by a sign
  let cond : Fin n → ((Fin d → ℂ) →ₗ[ℂ] ℂ) → Prop := fun j ψ =>
    ∃ ε : Fin 2, ∀ x, ψ (s j *ᵥ x) = (-1) ^ ε.val * ψ x
  have key : ∀ S : Finset (Fin n), ∀ ψ : (Fin d → ℂ) →ₗ[ℂ] ℂ, (∀ j ∉ S, cond j ψ) →
      ψ ∈ Submodule.span ℂ {ψ | ∃ e : Fin n → Fin 2, IsSignFunctional τ e ψ} := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro ψ hψ
      refine Submodule.subset_span ⟨fun j => Classical.choose (hψ j (Finset.notMem_empty j)),
        fun j x => ?_⟩
      exact Classical.choose_spec (hψ j (Finset.notMem_empty j)) x
    | insert j S hjS ih =>
      intro ψ hψ
      -- the two halves `ψ_± = (ψ ± ψ ∘ s_j) / 2`
      let σ : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := Matrix.toLin' (s j)
      have hσ : ∀ x, σ x = s j *ᵥ x := fun x => rfl
      let ψp : (Fin d → ℂ) →ₗ[ℂ] ℂ := (1 / 2 : ℂ) • (ψ + ψ ∘ₗ σ)
      let ψm : (Fin d → ℂ) →ₗ[ℂ] ℂ := (1 / 2 : ℂ) • (ψ - ψ ∘ₗ σ)
      have hsplit : ψ = ψp + ψm := by
        refine LinearMap.ext fun x => ?_
        simp only [ψp, ψm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          smul_eq_mul]
        ring
      have hssx : ∀ x, s j *ᵥ (s j *ᵥ x) = x := fun x => by
        rw [Matrix.mulVec_mulVec, hss, Matrix.one_mulVec]
      have hcondp : ∀ i ∉ S, cond i ψp := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          refine ⟨0, fun x => ?_⟩
          simp only [ψp, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, hσ,
            hssx, smul_eq_mul, Fin.val_zero, pow_zero, one_mul]
          ring
        · obtain ⟨ε, hε⟩ := hψ i (by simp [hij, hi])
          refine ⟨ε, fun x => ?_⟩
          simp only [ψp, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, hσ,
            smul_eq_mul]
          rw [Matrix.mulVec_mulVec, hcomm j i, ← Matrix.mulVec_mulVec, hε, hε]
          ring
      have hcondm : ∀ i ∉ S, cond i ψm := by
        intro i hi
        by_cases hij : i = j
        · subst hij
          refine ⟨1, fun x => ?_⟩
          simp only [ψm, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, hσ,
            hssx, smul_eq_mul, Fin.val_one, pow_one]
          ring
        · obtain ⟨ε, hε⟩ := hψ i (by simp [hij, hi])
          refine ⟨ε, fun x => ?_⟩
          simp only [ψm, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, hσ,
            smul_eq_mul]
          rw [Matrix.mulVec_mulVec, hcomm j i, ← Matrix.mulVec_mulVec, hε, hε]
          ring
      rw [hsplit]
      exact Submodule.add_mem _ (ih ψp hcondp) (ih ψm hcondm)
  exact key Finset.univ φ fun j hj => absurd (Finset.mem_univ j) hj

/-- The sign functionals separate the points of `ℂ^d`. -/
theorem eq_zero_of_signFunctional {d : ℕ}
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) {v : Fin d → ℂ}
    (hv : ∀ (e : Fin n → Fin 2) (φ : (Fin d → ℂ) →ₗ[ℂ] ℂ), IsSignFunctional τ e φ → φ v = 0) :
    v = 0 := by
  refine (_root_.Module.forall_dual_apply_eq_zero_iff ℂ v).mp fun φ => ?_
  have h := mem_span_signFunctional τ φ
  induction h using Submodule.span_induction with
  | mem ψ hψ =>
    obtain ⟨e, he⟩ := hψ
    exact hv e ψ he
  | zero => rfl
  | add ψ χ _ _ hψ hχ => rw [LinearMap.add_apply, hψ, hχ, add_zero]
  | smul c ψ _ hψ => rw [LinearMap.smul_apply, hψ, smul_zero]

end RealSubquotient

end Langlands.Archimedean
