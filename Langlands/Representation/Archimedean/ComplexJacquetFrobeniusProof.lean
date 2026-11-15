import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusFunction
import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Langlands.Representation.Archimedean.ComplexJacquetFrobenius
import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.Representation.Archimedean.ComplexDuality.LieInvariance

/-!
# Proof of Frobenius reciprocity for Jacquet functionals

Let `(ρ, π)` be a `(𝔤𝔩_n(ℂ), U(n))`-module on `V` and `ℓ` a nonzero Jacquet functional with
exponents `a`, `b`. By `IsComplexJacquetFunctional.exists_weight`, `b_j = i l_j` with
`l_j ∈ ℤ` and `ℓ` is an eigenfunctional of the diagonal unitary torus. The Frobenius map sends
`w` to the Frobenius function `f_w(β κ) = χ(β) ℓ(ρ(κ) w)` with `χ = borelChar l a`
(`ComplexJacquetFrobeniusFunction`). This file shows:

* `fderiv_one_frobeniusFunction`: the derivative at `1` of the extension of `f_u` to the
  matrices is `Y ↦ ℓ(π(1 ⊗ Y) u)`. Write `Y = P_u Y + N + diag(Re Y_jj)` with `P_u Y`
  skew-Hermitian and `N` strictly upper triangular, and differentiate along `exp(t P_u Y)`,
  `1 + t N` and `diag(e^{t Re Y_jj})`;
* `rightDerivative_frobeniusFunction`: `R(X) f_w = f_{π(1 ⊗ X) w}`, from the derivative at `1`
  by left equivariance under the Borel subgroup and right translation by `U(n)`;
* `complexJacquetFrobenius`: the proof of `ComplexJacquetFrobeniusStatement`, with the
  characters `d_j` of weight `l_j` and exponent `t_j = (a_j - (n - 1) + 2 j) / 2`.
-/

noncomputable section

open scoped TensorProduct Matrix Matrix.Norms.Operator ContDiff Topology Manifold

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

-- As in `GeneralLinear`: the charts on units and the operator norm on matrices need reduction
-- through the normed-ring instances.
set_option backward.isDefEq.respectTransparency false

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

universe uV

section Derivative

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V}
  {ℓ : V →ₗ[ℂ] ℂ} {l : Fin n → ℤ}

theorem isUnit_of_unitary (k : Matrix.unitaryGroup (Fin n) ℂ) :
    IsUnit (k : Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse (Unitary.star_mul_self_of_mem k.2))

/-- The extension of `f_w` to the matrices at `y = b k`, with `b` invertible upper triangular
and `k` unitary, is `χ(b) ℓ(ρ(k) w)`. -/
theorem unitsExtension_frobeniusFunction_eq (hT : IsTorusEigenfunctional ρ ℓ l)
    (α : Fin n → ℂ) (w : V) {y b : Matrix (Fin n) (Fin n) ℂ}
    (k : Matrix.unitaryGroup (Fin n) ℂ) (hb : b.IsUpperTriangular) (hbu : IsUnit b)
    (hy : y = b * (k : Matrix (Fin n) (Fin n) ℂ)) :
    unitsExtension (frobeniusFunction ρ ℓ l α w) y = borelChar l α b * ℓ (ρ k w) := by
  have hyu : IsUnit y := hy ▸ hbu.mul (isUnit_of_unitary k)
  rw [unitsExtension, dite_eq_left_of_eq_true (eq_true hyu)]
  exact frobeniusFunction_eq hT α w hyu.unit k hb hbu (by rw [IsUnit.unit_spec, hy])

variable {a b : Fin n → ℂ}

/-- **The derivative at the identity.** The derivative at `1` of the extension of `f_u` to
the matrices is `Y ↦ ℓ(π(1 ⊗ Y) u)`. -/
theorem fderiv_one_frobeniusFunction (hgk : IsComplexGKModule n ρ π)
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (hT : IsTorusEigenfunctional ρ ℓ l) (u : V)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (unitsExtension (frobeniusFunction ρ ℓ l a u)) 1 Y = ℓ (π (1 ⊗ₜ Y) u) := by
  set ψ := unitsExtension (frobeniusFunction ρ ℓ l a u) with hψ
  have hd : DifferentiableAt ℝ ψ 1 :=
    (contDiffAt_one_frobeniusFunction hgk hT a u).differentiableAt (by simp)
  set D := fderiv ℝ ψ 1 with hDdef
  have hD : HasFDerivAt ψ D 1 := hd.hasFDerivAt
  -- Skew-Hermitian directions: the curve `exp(tS)`.
  have hskew : ∀ S : Matrix (Fin n) (Fin n) ℂ, star S = -S → D S = ℓ (π (1 ⊗ₜ S) u) := by
    intro S hS
    have hD0 : HasFDerivAt ψ D ((fun t : ℝ => NormedSpace.exp (t • S)) 0) := by
      simpa using hD
    have h1 := hD0.comp_hasDerivAt 0 (hasDerivAt_exp_smul_zero S)
    have h2 := hasDerivAt_skewExp hgk hS ℓ u 0
    rw [skewExp_zero_smul hS, map_one, Module.End.one_apply] at h2
    have heq : (ψ ∘ fun t : ℝ => NormedSpace.exp (t • S)) =
        fun t : ℝ => ℓ (ρ (skewExp (t • S) (star_real_smul_of_skew hS t)) u) := by
      funext t
      rw [Function.comp_apply, hψ,
        unitsExtension_frobeniusFunction_eq hT a u (skewExp (t • S) (star_real_smul_of_skew hS t))
          Matrix.blockTriangular_one isUnit_one (by rw [coe_skewExp, Matrix.one_mul]),
        borelChar_one, one_mul]
    rw [heq] at h1
    exact h1.unique h2
  -- Strictly upper triangular directions: `ψ` is invariant under left multiplication by upper
  -- unipotent matrices, so the Library lemma `fderiv_strictUpper_mul_eq_zero` applies.
  have hnil : ∀ N : Matrix (Fin n) (Fin n) ℂ, (∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0) →
      D N = ℓ (π (1 ⊗ₜ N) u) := by
    intro N hN
    rw [hJ.1 N hN u]
    have hunip : ∀ v : upperUnipotent n ℂ,
        ψ (((v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) * 1) = ψ 1 := by
      intro v
      have hvu : ((v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular :=
        v.2.1
      have hvd : ∀ j, ((v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) j j = 1 :=
        v.2.2
      have hχ : borelChar l a ((v : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
          1 := by
        unfold borelChar
        simp only [hvd, borelFactor_one, Finset.prod_const_one]
      rw [hψ, unitsExtension_frobeniusFunction_eq hT a u 1 hvu
          (Units.isUnit (v : Langlands.GeneralLinear n ℂ)) (by simp),
        unitsExtension_frobeniusFunction_eq hT a u 1 Matrix.blockTriangular_one isUnit_one
          (by simp), hχ, borelChar_one]
    have h0 := ComplexDuality.LieInvariance.fderiv_strictUpper_mul_eq_zero hd hunip
      (N := N) fun i j hji => hN i j hji
    rwa [Matrix.mul_one] at h0
  -- Real diagonal directions: the curve `diag(e^{t r_j})`.
  have hdiag : ∀ r : Fin n → ℝ,
      D (Matrix.diagonal fun j => (r j : ℂ)) = (∑ j, (r j : ℂ) * a j) * ℓ u := by
    intro r
    set c : ℝ → Matrix (Fin n) (Fin n) ℂ :=
      fun t => Matrix.diagonal fun j => ((Real.exp (t * r j) : ℝ) : ℂ) with hcdef
    have hc : HasDerivAt c (Matrix.diagonal fun j => (r j : ℂ)) 0 := by
      refine hasDerivAt_matrix_of_entries fun i j => ?_
      by_cases hij : i = j
      · subst hij
        simp only [hcdef, Matrix.diagonal_apply_eq]
        have h := (((hasDerivAt_id (0 : ℝ)).mul_const (r i)).exp).ofReal_comp
        simpa using h
      · simp only [hcdef, Matrix.diagonal_apply_ne _ hij]
        exact hasDerivAt_const _ _
    have hD0 : HasFDerivAt ψ D (c 0) := by
      simpa [hcdef] using hD
    have h1 := hD0.comp_hasDerivAt 0 hc
    set K : ℂ := ∑ j, (r j : ℂ) * a j with hK
    have heq : (ψ ∘ c) = fun t : ℝ => Complex.exp ((t : ℂ) * K) * ℓ u := by
      funext t
      have hup : (c t).IsUpperTriangular := Matrix.blockTriangular_diagonal _
      have hd0 : ∀ j, c t j j ≠ 0 := fun j => by
        simp only [hcdef, Matrix.diagonal_apply_eq]
        exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
      rw [Function.comp_apply, hψ,
        unitsExtension_frobeniusFunction_eq hT a u 1 hup (isUnit_of_upper hup hd0) (by simp),
        map_one, Module.End.one_apply]
      congr 1
      unfold borelChar
      simp only [hcdef, Matrix.diagonal_apply_eq, borelFactor_exp]
      rw [← Complex.exp_sum, hK, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      ring
    rw [heq] at h1
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K) * ℓ u) (K * ℓ u) 0 := by
      have h := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const K).cexp).mul_const (ℓ u)
      simpa using h
    exact h1.unique h2
  -- Assembly: `Y = P_u Y + N + diag(Re Y_jj)`.
  set S := skewPart Y with hS
  set Dg : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j => (((Y j j).re : ℝ) : ℂ) with hDg
  set N := upperPart Y - Dg with hNdef
  have hN : ∀ i j : Fin n, (j : ℕ) ≤ i → N i j = 0 := by
    intro i j hji
    rw [hNdef, Matrix.sub_apply]
    rcases Nat.lt_or_eq_of_le hji with h | h
    · have hlt : j < i := h
      rw [upperPart_isUpperTriangular Y hlt, hDg, Matrix.diagonal_apply_ne _ (ne_of_gt hlt),
        sub_zero]
    · have he : j = i := Fin.ext h
      subst he
      rw [upperPart_diag, hDg, Matrix.diagonal_apply_eq, sub_self]
  have hY : Y = N + Dg + S := by
    rw [hNdef, sub_add_cancel, hS, upperPart_add_skewPart]
  have hΛDg : ℓ (π (1 ⊗ₜ Dg) u) = (∑ j, (((Y j j).re : ℝ) : ℂ) * a j) * ℓ u := by
    rw [hJ.apply_upper Dg (Matrix.blockTriangular_diagonal _) u]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hDg]
  rw [hY, map_add, map_add, lie_one_tmul_add, lie_one_tmul_add, map_add, map_add,
    hnil N hN, hskew S (star_skewPart Y), hΛDg, hDg, hdiag]

/-- **The right derivatives of the Frobenius functions.** `R(X) f_w = f_{π(1 ⊗ X) w}`. At
`g = β κ`, `R(X) f_w(g) = χ(β) R(κ X κ*) f_{ρ(κ) w}(1) = χ(β) ℓ(π(1 ⊗ κ X κ*) ρ(κ) w)
= χ(β) ℓ(ρ(κ) π(1 ⊗ X) w)`. -/
theorem rightDerivative_frobeniusFunction (hgk : IsComplexGKModule n ρ π)
    (hJ : IsComplexJacquetFunctional n π ℓ a b) (hT : IsTorusEigenfunctional ρ ℓ l) (w : V)
    (X : Matrix (Fin n) (Fin n) ℂ) (g : Langlands.GeneralLinear n ℂ) :
    rightDerivative (matrixModel ℂ n) X (frobeniusFunction ρ ℓ l a w) g =
      frobeniusFunction ρ ℓ l a (π (1 ⊗ₜ X) w) g := by
  have hf := contMDiff_frobeniusFunction hgk hT a w
  obtain ⟨hβ, hβu, hg⟩ := iwasawa_spec g
  set β := iwasawaB g with hβdef
  set κ := iwasawaK g with hκdef
  set βU : Langlands.GeneralLinear n ℂ := hβu.unit with hβU
  set κU : Langlands.GeneralLinear n ℂ := Unitary.toUnits κ with hκU
  have hβc : (βU : Matrix (Fin n) (Fin n) ℂ) = β := IsUnit.unit_spec hβu
  have hκc : (κU : Matrix (Fin n) (Fin n) ℂ) = κ := rfl
  have hκi : ((κU⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      star (κ : Matrix (Fin n) (Fin n) ℂ) := rfl
  have hgU : g = βU * κU := by
    apply Units.ext
    rw [Units.val_mul, hβc, hκc, hg]
  -- Left equivariance under `β`.
  have hleft : ∀ g', frobeniusFunction ρ ℓ l a w (βU * g') =
      borelChar l a β * frobeniusFunction ρ ℓ l a w g' := fun g' => by
    have h := frobeniusFunction_mul_left hT a w βU g' (by rw [hβc]; exact hβ)
    rwa [hβc] at h
  rw [hgU, rightDerivative_mul_left_of_eq hf hleft X κU]
  -- Right translation by `κ`.
  have htr := congrFun (rightTranslation_rightDerivative hf X κU) 1
  change rightDerivative (matrixModel ℂ n) X (frobeniusFunction ρ ℓ l a w) (1 * κU) = _ at htr
  rw [one_mul] at htr
  have hfk : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) κU
      (frobeniusFunction ρ ℓ l a w) = frobeniusFunction ρ ℓ l a (ρ κ w) := by
    funext g'
    exact frobeniusFunction_mul_unitary hT a w g' κU κ hκc
  rw [hfk, hκc, hκi] at htr
  rw [htr]
  -- The derivative at `1`.
  have hf' := contMDiff_frobeniusFunction hgk hT a (ρ κ w)
  rw [rightDerivative_eq_fderiv hf', Units.val_one, Matrix.one_mul,
    fderiv_one_frobeniusFunction hgk hJ hT, ← hgk.2.2.2 κ X w]
  -- Compare with the definition of `f_{π(1 ⊗ X) w}` at `g`.
  rw [← hgU]
  rfl

end Derivative

/-! ## Frobenius reciprocity -/

section Frobenius

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}
  {ℓ : V →ₗ[ℂ] ℂ} {l : Fin n → ℤ}

/-- The Frobenius functions as a linear map `w ↦ f_w`. -/
def frobeniusMap (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V)
    (ℓ : V →ₗ[ℂ] ℂ) (l : Fin n → ℤ) (α : Fin n → ℂ) :
    V →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun := frobeniusFunction ρ ℓ l α
  map_add' := frobeniusFunction_add α
  map_smul' := frobeniusFunction_smul α

/-- The Frobenius functions are `U(n)`-finite: the right translates of `f_w` are the
functions `f_{ρ(k) w}`, which lie in the image of the finite-dimensional orbit span of `w`. -/
theorem frobeniusFunction_mem_kFiniteVectors (hT : IsTorusEigenfunctional ρ ℓ l)
    (α : Fin n → ℂ) (w : V) (hw : FiniteVectors.IsFiniteVector ρ w) :
    frobeniusFunction ρ ℓ l α w ∈
      kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
        (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff]
  have hfin : Module.Finite ℂ (FiniteVectors.orbitSpan ρ w) := hw
  refine Submodule.finiteDimensional_of_le (Submodule.span_le.mpr ?_ :
    _ ≤ (FiniteVectors.orbitSpan ρ w).map (frobeniusMap ρ ℓ l α))
  rintro _ ⟨k, rfl⟩
  refine ⟨ρ ⟨((k : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ), k.2⟩ w,
    FiniteVectors.action_mem_orbitSpan ρ _ w, ?_⟩
  funext g
  exact (frobeniusFunction_mul_unitary hT α w g k _ rfl).symm

/-- **Frobenius reciprocity for Jacquet functionals.** -/
theorem complexJacquetFrobenius : ComplexJacquetFrobeniusStatement.{uV} := by
  intro n V _ _ ρ π hgk ℓ a b hℓ hJ
  obtain ⟨l, hl, hT⟩ := hJ.exists_weight hgk hℓ
  set d : Fin n → ComplexCharacterData := fun j =>
    characterOfParams (l j) ((a j - ((n : ℂ) - 1) + 2 * ((j : ℕ) : ℂ)) / 2) with hd
  have hda : ∀ j : Fin n, 2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) = a j := by
    intro j
    simp only [hd, characterOfParams_exponent]
    ring
  have hdl : ∀ j : Fin n, (d j).weight = l j := fun j => by simp [hd]
  refine ⟨d, hda, fun j => by rw [hdl, hl j], ?_⟩
  have hmem : ∀ w : V, frobeniusFunction ρ ℓ l a w ∈
      kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) := by
    intro w
    refine ⟨⟨contMDiff_frobeniusFunction hgk hT a w, fun a' u g => ?_⟩,
      frobeniusFunction_mem_kFiniteVectors hT a w (hgk.1 w)⟩
    rw [frobeniusFunction_diagonal_mul hT a w a' u g, principalSeriesCharacter_ofFn]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hdl, hda]
  let B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n (List.ofFn d))
      (unitaryCompact ℂ n) :=
    { toFun := fun w => ⟨frobeniusFunction ρ ℓ l a w, hmem w⟩
      map_add' := fun w w' => Subtype.ext (frobeniusFunction_add a w w')
      map_smul' := fun c w => Subtype.ext (frobeniusFunction_smul a c w) }
  have hB : ∀ w, (B w : Langlands.GeneralLinear n ℂ → ℂ) = frobeniusFunction ρ ℓ l a w :=
    fun _ => rfl
  refine ⟨B, ?_, ⟨fun k v => ?_, fun X v => ?_⟩⟩
  · -- `B ≠ 0`: `f_w(1) = ℓ(w)`.
    obtain ⟨w, hw⟩ : ∃ w, ℓ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hℓ (LinearMap.ext h)
    intro hB0
    have h1 := congrFun (congrArg Subtype.val (LinearMap.congr_fun hB0 w)) 1
    rw [hB] at h1
    have h2 := frobeniusFunction_eq hT a w 1 1 Matrix.blockTriangular_one isUnit_one (by simp)
    rw [borelChar_one, one_mul, map_one, Module.End.one_apply] at h2
    rw [h2] at h1
    exact hw h1
  · rw [hB, hB]
    funext g
    exact (frobeniusFunction_mul_unitary hT a v g k _ rfl).symm
  · rw [hB, hB]
    funext g
    exact (rightDerivative_frobeniusFunction hgk hJ hT v X g).symm

end Frobenius

end Langlands.Archimedean
