import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# From the Lie algebra to `U(n)`, and the spherical vector

Two tools for `(𝔤𝔩_n(ℂ), U(n))`-modules.

* **Lie algebra to group** (`ComplexSphericalLieGroup.map_rho_of_map_pi`). Let `(ρ, π)` be a
  `(𝔤𝔩_n(ℂ), U(n))`-module on `V`, `σ` a representation of `U(n)` on a finite-dimensional space
  `F` whose derivative along the curves of `U(n)` through `1` is given by a map
  `σ' : M_n(ℂ) → End F`, and `ψ : F → V` a linear map with `ψ ∘ σ'(Y) = π(1 ⊗ Y) ∘ ψ` for
  every skew-Hermitian `Y`. Then `ψ ∘ σ(k) = ρ(k) ∘ ψ` for every `k ∈ U(n)`.

  Every unitary matrix is the exponential of a skew-Hermitian matrix
  (`exists_skew_exp_eq`: `Y = cfc (z ↦ i arg z) k`, by the continuous functional calculus of
  the C⋆-algebra `M_n(ℂ)`; the spectrum of `k` is finite, so `arg` is continuous on it). Along
  `t ↦ exp(tY)`, for every linear functional `μ` on `V`, the functions
  `c_x(t) = μ(ψ(σ(exp tY) x)) − μ(ρ(exp tY) ψ(x))` satisfy `c_x' = c_{σ'(Y) x}` and `c_x(0) = 0`.
  In a basis `b` of `F` this is the linear ODE `r' = r A` for the row vector `r_j = c_{b_j}`,
  whose only solution with `r(0) = 0` is `0` (`ODE_solution_unique_univ`).

* **Spherical vector** (`ComplexSphericalLieGroup.exists_spherical`). If all characters of `ds`
  have weight `0`, the standard module of `ds` contains a `U(n)`-fixed `U(n)`-finite function `T`
  with `T(1) = 1`: the extension of the constant function `1` on `U(n)`
  (`complexPrincipalSeriesExtension`).
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

-- As in `ComplexJacquetTorus`: the operator norm on matrices needs reduction through the
-- normed-ring instances.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

universe uV uF

namespace ComplexSphericalLieGroup

/-! ## Every unitary matrix is an exponential -/

section Exp

variable {n : ℕ}

open Complex in
open scoped Matrix.Norms.L2Operator in
/-- Every unitary matrix `u` is `exp Y` for a skew-Hermitian `Y`, namely
`Y = cfc (z ↦ i arg z) u`. -/
theorem exists_skew_exp_eq (u : Matrix (Fin n) (Fin n) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y ∧ NormedSpace.exp Y = u := by
  have hu' : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := hu
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu'
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  refine ⟨cfc (fun z : ℂ => I * (arg z : ℂ)) u, ?_, ?_⟩
  · rw [← cfc_star, ← cfc_neg]
    refine cfc_congr fun z _ => ?_
    simp [Complex.conj_ofReal]
  · have hcont : ContinuousOn (fun z : ℂ => I * (arg z : ℂ)) (spectrum ℂ u) :=
      hfin.continuousOn _
    have hcont' : ContinuousOn (NormedSpace.exp : ℂ → ℂ)
        ((fun z : ℂ => I * (arg z : ℂ)) '' spectrum ℂ u) :=
      NormedSpace.exp_continuous.continuousOn
    rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp' _ _ u hcont' hcont]
    conv_rhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun y hy => ?_
    have hy1 : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary hu' hy
    have hlog : I * (arg y : ℂ) = log y :=
      Complex.ext (by simp [log_re, hy1]) (by simp [log_im])
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy1
    simpa [← exp_eq_exp_ℂ, hlog] using exp_log hy0

/-- Every element of `U(n)` is `skewExp Y` for some skew-Hermitian `Y`. -/
theorem exists_skewExp_eq (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ (Y : Matrix (Fin n) (Fin n) ℂ) (hY : star Y = -Y), skewExp Y hY = k := by
  obtain ⟨Y, hY, hk⟩ := exists_skew_exp_eq (k : Matrix (Fin n) (Fin n) ℂ) k.2
  exact ⟨Y, hY, Subtype.ext (by rw [coe_skewExp, hk])⟩

end Exp

/-! ## Lie algebra to group -/

section LieGroup

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {F : Type uF} [AddCommGroup F] [Module ℂ F]

/-- Shifting a derivative at `0` along `t ↦ exp(tY)` to a derivative at `s`. -/
theorem hasDerivAt_shift (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) F)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) (D : F → F)
    (h0 : ∀ (w : F) (ℓ : F →ₗ[ℂ] ℂ),
      HasDerivAt (fun t : ℝ => ℓ (σ (skewExp (t • Y) (star_real_smul_of_skew hY t)) w))
        (ℓ (D w)) 0)
    (ℓ : F →ₗ[ℂ] ℂ) (w : F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (skewExp (t • Y) (star_real_smul_of_skew hY t)) w))
      (ℓ (σ (skewExp (s • Y) (star_real_smul_of_skew hY s)) (D w))) s := by
  set k : ℝ → Matrix.unitaryGroup (Fin n) ℂ :=
    fun t => skewExp (t • Y) (star_real_smul_of_skew hY t) with hk
  have h1 : HasDerivAt (fun t => (ℓ ∘ₗ σ (k s)) (σ (k t) w))
      ((ℓ ∘ₗ σ (k s)) (D w)) (s - s) := by
    rw [sub_self]
    exact h0 w (ℓ ∘ₗ σ (k s))
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  change ℓ (σ (k t) w) = ℓ (σ (k s) (σ (k (t - s)) w))
  rw [← Module.End.mul_apply, ← map_mul, hk, ← skewExp_add_smul hY, add_sub_cancel]

/-- Uniqueness for the linear ODE `r' = r A` on row vectors: a solution vanishing at `0`
vanishes everywhere. -/
theorem eq_zero_of_hasDerivAt_vecMul {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    {r : ℝ → Fin m → ℂ} (h : ∀ t, HasDerivAt r (r t ᵥ* A) t) (h0 : r 0 = 0) : r = 0 := by
  set L : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.vecMulLinear A) with hL
  have hLapp : ∀ x, L x = x ᵥ* A := fun x => rfl
  refine ODE_solution_unique_univ (v := fun _ => L) (s := fun _ => Set.univ) (t₀ := 0)
    (fun _ => L.lipschitzWith.lipschitzOnWith) (fun t => ⟨?_, trivial⟩) (fun t => ⟨?_, trivial⟩) ?_
  · rw [hLapp]
    exact h t
  · simp only [Pi.zero_apply, map_zero]
    exact hasDerivAt_const t (0 : Fin m → ℂ)
  · rw [h0]
    rfl

variable [FiniteDimensional ℂ F]

/-- **Lie algebra to group along one exponential.** -/
theorem map_rho_skewExp_of_map_pi (hgk : IsComplexGKModule n ρ π)
    (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) F)
    (σ' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ F)
    (hσ : ∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
      star X = -X → γ 0 = 1 →
      (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0) →
        ∀ (w : F) (ℓ : F →ₗ[ℂ] ℂ), HasDerivAt (fun t => ℓ (σ (γ t) w)) (ℓ (σ' X w)) 0)
    (ψ : F →ₗ[ℂ] V)
    (hψ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w, ψ (σ' Y w) = π (1 ⊗ₜ Y) (ψ w))
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) (w : F) :
    ψ (σ (skewExp Y hY) w) = ρ (skewExp Y hY) (ψ w) := by
  set k : ℝ → Matrix.unitaryGroup (Fin n) ℂ :=
    fun t => skewExp (t • Y) (star_real_smul_of_skew hY t) with hk
  -- the defect `D t = ψ ∘ σ(k t) − ρ(k t) ∘ ψ`, tested against a functional `μ`
  set D : ℝ → (V →ₗ[ℂ] ℂ) → F →ₗ[ℂ] ℂ :=
    fun t μ => μ ∘ₗ (ψ ∘ₗ σ (k t) - ρ (k t) ∘ₗ ψ) with hD
  have hDapp : ∀ t μ x, D t μ x = μ (ψ (σ (k t) x)) - μ (ρ (k t) (ψ x)) := by
    intro t μ x
    simp [hD]
  have hderiv : ∀ (μ : V →ₗ[ℂ] ℂ) (x : F) (s : ℝ),
      HasDerivAt (fun t => D t μ x) (D s μ (σ' Y x)) s := by
    intro μ x s
    have h1 := hasDerivAt_shift σ hY (σ' Y)
      (fun w' ℓ => hσ k Y hY (skewExp_zero_smul hY) (hasDerivAt_skewExp_entry hY) w' ℓ)
      (μ ∘ₗ ψ) x s
    have h2 := hasDerivAt_skewExp hgk hY μ (ψ x) s
    rw [← hψ Y hY x] at h2
    simp only [hDapp]
    exact h1.sub h2
  have hzero : ∀ μ : V →ₗ[ℂ] ℂ, ∀ x, D 0 μ x = 0 := by
    intro μ x
    rw [hDapp]
    have h0 : k 0 = 1 := skewExp_zero_smul hY
    rw [h0, map_one, map_one, Module.End.one_apply, Module.End.one_apply, sub_self]
  -- coordinates in a basis
  set b := Module.finBasis ℂ F with hb
  set A : Matrix (Fin (Module.finrank ℂ F)) (Fin (Module.finrank ℂ F)) ℂ :=
    fun i j => b.repr (σ' Y (b j)) i with hA
  have hsum : ∀ t μ j, D t μ (σ' Y (b j)) = ∑ i, D t μ (b i) * A i j := by
    intro t μ j
    conv_lhs => rw [← b.sum_repr (σ' Y (b j))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hall : ∀ μ : V →ₗ[ℂ] ℂ, ∀ t, D t μ = 0 := by
    intro μ
    have hr := eq_zero_of_hasDerivAt_vecMul (A := A) (r := fun t j => D t μ (b j))
      (fun t => hasDerivAt_pi.mpr fun j => by
        have := hderiv μ (b j) t
        rw [hsum] at this
        exact this)
      (funext fun j => hzero μ (b j))
    intro t
    refine b.ext fun j => ?_
    have := congrFun (congrFun hr t) j
    simpa using this
  have h1 : k 1 = skewExp Y hY := Subtype.ext (by simp [hk, coe_skewExp])
  have hv : ψ (σ (k 1) w) - ρ (k 1) (ψ w) = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun μ => ?_
    have := hall μ 1
    have h' := congrArg (fun f : F →ₗ[ℂ] ℂ => f w) this
    simp only [hDapp, LinearMap.zero_apply] at h'
    rw [map_sub]
    exact h'
  rw [← h1]
  exact sub_eq_zero.mp hv

/-- **Lie algebra to group.** Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module, `σ` a representation
of `U(n)` on a finite-dimensional space `F` with derivative `σ'` along the curves of `U(n)`
through `1`, and `ψ : F → V` linear with `ψ ∘ σ'(Y) = π(1 ⊗ Y) ∘ ψ` for skew-Hermitian `Y`.
Then `ψ ∘ σ(k) = ρ(k) ∘ ψ` for every `k ∈ U(n)`. -/
theorem map_rho_of_map_pi (hgk : IsComplexGKModule n ρ π)
    (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) F)
    (σ' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ F)
    (hσ : ∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
      star X = -X → γ 0 = 1 →
      (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0) →
        ∀ (w : F) (ℓ : F →ₗ[ℂ] ℂ), HasDerivAt (fun t => ℓ (σ (γ t) w)) (ℓ (σ' X w)) 0)
    (ψ : F →ₗ[ℂ] V)
    (hψ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w, ψ (σ' Y w) = π (1 ⊗ₜ Y) (ψ w)) :
    ∀ k w, ψ (σ k w) = ρ k (ψ w) := by
  intro k w
  obtain ⟨Y, hY, rfl⟩ := exists_skewExp_eq k
  exact map_rho_skewExp_of_map_pi hgk σ σ' hσ ψ hψ hY w

end LieGroup

/-! ## The spherical vector -/

section Spherical

open ComplexPrincipalSeriesExtension ComplexGramFormula

/-- With all weights `0`, the position characters are trivial on unit complex numbers. -/
theorem complexPositionCharacter_phaseUnit :
    ∀ (ds : List ComplexCharacterData), (∀ d ∈ ds, d.weight = 0) →
      ∀ (l : ℕ) (z : ℂˣ), complexPositionCharacter ds l (phaseUnit z) = 1
  | [], _, _, _ => rfl
  | d :: _, hw, 0, z => by
      simp only [complexPositionCharacter]
      rw [d.character_eq, hw d List.mem_cons_self, norm_phaseUnit, zpow_zero, one_mul,
        Complex.ofReal_one, Complex.one_cpow]
  | _ :: ds, hw, p + 1, z => by
      simp only [complexPositionCharacter]
      exact complexPositionCharacter_phaseUnit ds
        (fun d hd => hw d (List.mem_cons_of_mem _ hd)) p z

theorem principalSeriesCharacter_phaseUnit {n : ℕ} {ds : List ComplexCharacterData}
    (hw : ∀ d ∈ ds, d.weight = 0) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun i => phaseUnit (a i)) = 1 := by
  unfold principalSeriesCharacter
  refine Finset.prod_eq_one fun i _ => ?_
  rw [complexPositionCharacter_phaseUnit ds hw, norm_phaseUnit, one_pow, Complex.ofReal_one,
    Complex.one_cpow, mul_one]

/-- **Spherical vector.** If every character of `ds` has weight `0`, the `U(n)`-finite functions
of the standard module of `ds` contain a `U(n)`-fixed vector `T` with `T(1) = 1`. -/
theorem exists_spherical {n : ℕ} {ds : List ComplexCharacterData}
    (hw : ∀ d ∈ ds, d.weight = 0) :
    ∃ T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      (∀ k : Matrix.unitaryGroup (Fin n) ℂ, complexStandardRep n ds k T = T) ∧
        kFiniteEval (complexStandardModule n ds) 1 T = 1 := by
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ =>
        fun x : Matrix.unitaryGroup (Fin n) ℂ => (fun _ => (1 : ℂ)) (x * k))) := by
    refine FiniteDimensional.span_of_finite ℂ
      ((Set.finite_singleton (fun _ : Matrix.unitaryGroup (Fin n) ℂ => (1 : ℂ))).subset ?_)
    rintro _ ⟨k, rfl⟩
    rfl
  obtain ⟨f, hf, hfk⟩ := complexPrincipalSeriesExtension n ds (fun _ => (1 : ℂ))
    continuous_const hfin (fun a κ => by
      rw [principalSeriesCharacter_phaseUnit hw, one_mul])
  refine ⟨⟨f, hf⟩, fun k => ?_, ?_⟩
  · apply Subtype.ext
    rw [principalSeriesRep_apply_coe]
    have hfps : f ∈ principalSeries ℂ n (complexPositionCharacter ds) := (Submodule.mem_inf.mp hf).1
    refine eq_of_eqOn_unitary (rightTranslation_mem_principalSeries _ hfps _) hfps
      fun g hg => ?_
    have hgu : g = Unitary.toUnits (⟨(g : Matrix (Fin n) (Fin n) ℂ), hg⟩ :
        Matrix.unitaryGroup (Fin n) ℂ) := Units.ext rfl
    change f (g * Unitary.toUnits k) = f g
    rw [hgu, ← map_mul, hfk, hfk]
  · rw [kFiniteEval_apply]
    have h1 : (1 : Langlands.GeneralLinear n ℂ) =
        Unitary.toUnits (1 : Matrix.unitaryGroup (Fin n) ℂ) := (map_one _).symm
    change f 1 = 1
    rw [h1, hfk]

end Spherical

end ComplexSphericalLieGroup

open ComplexSphericalLieGroup

/-- **Statement (Lie algebra to group, and the spherical vector).**

1. Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on `V` (`IsComplexGKModule`), `σ` a representation
   of `U(n)` on a finite-dimensional space `F` and `σ' : M_n(ℂ) → End F` any map such that for
   every curve `γ` in `U(n)` with `γ(0) = 1` whose entries are differentiable at `0` with
   skew-Hermitian derivative matrix `X`, every `w ∈ F` and every linear functional `ℓ` on `F`,
   `t ↦ ℓ(σ(γ t) w)` has derivative `ℓ(σ'(X) w)` at `0`. If a linear map `ψ : F → V` satisfies
   `ψ(σ'(Y) w) = π(1 ⊗ Y) ψ(w)` for every skew-Hermitian `Y`, then
   `ψ(σ(k) w) = ρ(k) ψ(w)` for every `k ∈ U(n)` and `w ∈ F`.
2. If every character in the list `ds` has weight `0`, then the `U(n)`-finite functions of the
   standard module of `ds` on `GL_n(ℂ)` contain a function `T` fixed by right translation by
   every `k ∈ U(n)` with `T(1) = 1`. -/
def ComplexSphericalLieGroupStatement : Prop :=
  (∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsComplexGKModule n ρ π →
    ∀ (F : Type uF) [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
      (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) F)
      (σ' : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ F),
      (∀ (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
        star X = -X → γ 0 = 1 →
        (∀ i j, HasDerivAt (fun t => (γ t : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0) →
          ∀ (w : F) (ℓ : F →ₗ[ℂ] ℂ), HasDerivAt (fun t => ℓ (σ (γ t) w)) (ℓ (σ' X w)) 0) →
      ∀ ψ : F →ₗ[ℂ] V,
        (∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → ∀ w, ψ (σ' Y w) = π (1 ⊗ₜ Y) (ψ w)) →
        ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (w : F), ψ (σ k w) = ρ k (ψ w)) ∧
  ∀ (n : ℕ) (ds : List ComplexCharacterData), (∀ d ∈ ds, d.weight = 0) →
    ∃ T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
      (∀ k : Matrix.unitaryGroup (Fin n) ℂ, complexStandardRep n ds k T = T) ∧
        kFiniteEval (complexStandardModule n ds) 1 T = 1

theorem complexSphericalLieGroup : ComplexSphericalLieGroupStatement.{uV, uF} :=
  ⟨fun _ _ _ _ _ _ hgk _ _ _ _ σ σ' hσ ψ hψ => map_rho_of_map_pi hgk σ σ' hσ ψ hψ,
    fun _ _ hw => exists_spherical hw⟩

end Langlands.Archimedean
