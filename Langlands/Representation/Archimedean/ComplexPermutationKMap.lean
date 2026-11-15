import Langlands.Representation.Archimedean.ComplexPermutationKType
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusFunction

/-!
# `U(n)`-isomorphic principal series

Restricted to `U(n)`, the principal series of `d 0, …, d (n-1)` and of a rearrangement
`d (σ⁻¹ 0), …, d (σ⁻¹ (n-1))` are isomorphic: both are induced from the diagonal unitary torus,
and the permutation matrix `P` of `σ` conjugates the two torus characters. This file constructs
an injective `U(n)`-equivariant linear map between their `U(n)`-finite functions (in both
directions, by symmetry), which is all that the upgrade lemmas of `ComplexPermutationKType`
need.

The map is `f ↦ F`, `F(β κ) = χ'(β) f(P κ)` for `β` upper triangular and `κ` unitary, where `χ'`
is the Borel character of the rearranged list. It is the Frobenius function
(`frobeniusFunction`, `ComplexJacquetFrobeniusFunction`) of the functional `f ↦ f(P)`, which
transforms under the diagonal unitary torus by the rearranged weights
(`isTorusEigenfunctional_evalPerm`). The Frobenius function is smooth, satisfies the
principal series law of the rearranged list, and commutes with right translation by `U(n)`;
it is injective because `F(P⁻¹ κ) = f(κ)` for unitary `κ`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Archimedean.ComplexPermutation

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean Langlands.Archimedean.ComplexDuality

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-! ## Permutation matrices -/

/-- The permutation matrix of `σ`, with `P i j = 1` exactly when `j = σ i`, as a unitary
matrix. -/
def permUnitary (σ : Equiv.Perm (Fin n)) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel,
      Matrix.permMatrix_one]⟩

theorem permUnitary_coe (σ : Equiv.Perm (Fin n)) :
    ((permUnitary σ : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      σ.permMatrix ℂ :=
  rfl

/-- `P m = diag(m (σ j) (σ j)) P` for a diagonal matrix `m`. -/
theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin n)) (m : Matrix (Fin n) (Fin n) ℂ)
    (hm : ∀ i j, i ≠ j → m i j = 0) :
    σ.permMatrix ℂ * m = Matrix.diagonal (fun j => m (σ j) (σ j)) * σ.permMatrix ℂ := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.submatrix_apply, id, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq]
  by_cases h : σ i = j
  · subst h
    simp
  · rw [hm _ _ h]
    simp [h]

/-! ## The torus eigenfunctional `f ↦ f(P)` -/

/-- Evaluation at the permutation matrix of `σ`. -/
def evalPerm (ds : List ComplexCharacterData) (σ : Equiv.Perm (Fin n)) : (KF n ds) →ₗ[ℂ] ℂ :=
  kFiniteEval (complexStandardModule n ds) (Unitary.toUnits (permUnitary σ))

/-- `f ↦ f(P)` transforms under the diagonal unitary torus by the rearranged weights
`k ↦ (d (σ⁻¹ k)).weight`: `f(P m) = f(diag(m (σ j) (σ j)) P) = ∏ⱼ m (σ j) (σ j)^{l_j} f(P)`. -/
theorem isTorusEigenfunctional_evalPerm (d : Fin n → ComplexCharacterData)
    (σ : Equiv.Perm (Fin n)) :
    IsTorusEigenfunctional (complexStandardRep n (List.ofFn d)) (evalPerm (List.ofFn d) σ)
      (fun k => (d (σ.symm k)).weight) := by
  intro m hm f
  have hmu := m.2
  have hnorm : ∀ j, ‖(m : Matrix (Fin n) (Fin n) ℂ) j j‖ = 1 :=
    norm_diag_eq_one_of_unitary hmu hm
  have hne : ∀ j, (m : Matrix (Fin n) (Fin n) ℂ) j j ≠ 0 := fun j h => by
    have := hnorm j
    rw [h, norm_zero] at this
    exact zero_ne_one this
  let a : Fin n → ℂˣ := fun j => Units.mk0 ((m : Matrix (Fin n) (Fin n) ℂ) (σ j) (σ j)) (hne _)
  have hfac : (Unitary.toUnits (permUnitary σ) * Unitary.toUnits m :
      Langlands.GeneralLinear n ℂ) =
      (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        ((1 : upperUnipotent n ℂ) : Langlands.GeneralLinear n ℂ) *
        Unitary.toUnits (permUnitary σ) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one,
      Matrix.mul_one, Iwasawa.diagonalUnits_val]
    exact permMatrix_mul_diagonal σ _ hm
  change (f : Langlands.GeneralLinear n ℂ → ℂ)
      (Unitary.toUnits (permUnitary σ) * Unitary.toUnits m) =
    _ * (f : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits (permUnitary σ))
  rw [hfac, f.2.1.2 a 1, principalSeriesCharacter_ofFn]
  congr 1
  rw [← Equiv.prod_comp σ (fun k => ((m : Matrix (Fin n) (Fin n) ℂ) k k) ^
    (d (σ.symm k)).weight)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [show ((a j : ℂˣ) : ℂ) = (m : Matrix (Fin n) (Fin n) ℂ) (σ j) (σ j) from rfl,
    borelFactor_of_norm_eq_one _ _ (hnorm (σ j)), Equiv.symm_apply_apply]

/-! ## The map -/

/-- The Borel exponents `2 t + (n - 1) - 2 k` of the rearranged list. -/
def permExponent (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n)) (k : Fin n) : ℂ :=
  2 * (d (σ.symm k)).exponent + ((n : ℂ) - 1) - 2 * ((k : ℕ) : ℂ)

/-- The function `F(β κ) = χ'(β) f(P κ)`. -/
def permFunction (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n))
    (f : KF n (List.ofFn d)) : Langlands.GeneralLinear n ℂ → ℂ :=
  frobeniusFunction (complexStandardRep n (List.ofFn d)) (evalPerm (List.ofFn d) σ)
    (fun k => (d (σ.symm k)).weight) (permExponent d σ) f

/-- `permFunction` as a linear map into functions. -/
def permFunctionLinear (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n)) :
    (KF n (List.ofFn d)) →ₗ[ℂ] (Langlands.GeneralLinear n ℂ → ℂ) where
  toFun := permFunction d σ
  map_add' f g := frobeniusFunction_add _ f g
  map_smul' c f := frobeniusFunction_smul _ c f

/-- Right translation: `F_f(g k) = F_{ρ(k) f}(g)`. -/
theorem permFunction_rightTranslation (d : Fin n → ComplexCharacterData)
    (σ : Equiv.Perm (Fin n)) (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn d)) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (Unitary.toUnits k)
        (permFunction d σ f) =
      permFunction d σ (complexStandardRep n (List.ofFn d) k f) := by
  funext g
  exact frobeniusFunction_mul_unitary (isTorusEigenfunctional_evalPerm d σ) _ f g
    (Unitary.toUnits k) k rfl

/-- `F_f` lies in the principal series of the rearranged list. -/
theorem permFunction_mem (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n))
    (f : KF n (List.ofFn d)) :
    permFunction d σ f ∈ complexStandardModule n (List.ofFn fun k => d (σ.symm k)) := by
  refine ⟨contMDiff_frobeniusFunction (isComplexGKModule_complexStandardModule n _)
    (isTorusEigenfunctional_evalPerm d σ) _ f, fun a u g => ?_⟩
  rw [permFunction, frobeniusFunction_diagonal_mul (isTorusEigenfunctional_evalPerm d σ),
    principalSeriesCharacter_ofFn]
  rfl

/-- `F_f` is `U(n)`-finite. -/
theorem permFunction_mem_kFinite (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n))
    (f : KF n (List.ofFn d)) :
    permFunction d σ f ∈ KF n (List.ofFn fun k => d (σ.symm k)) := by
  refine ⟨permFunction_mem d σ f, ?_⟩
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  have hfin : FiniteDimensional ℂ
      (FiniteVectors.orbitSpan (complexStandardRep n (List.ofFn d)) f) :=
    isFiniteVector_complexStandardRep _ f
  refine Submodule.finiteDimensional_of_le (S₂ := ((FiniteVectors.orbitSpan
    (complexStandardRep n (List.ofFn d)) f).map (permFunctionLinear d σ))) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨complexStandardRep n (List.ofFn d) (toUnitary k) f,
    FiniteVectors.action_mem_orbitSpan _ _ _, ?_⟩
  change permFunction d σ _ = _
  rw [← permFunction_rightTranslation, toUnits_toUnitary]

/-- The map `f ↦ F_f` between the `U(n)`-finite functions. -/
def permKMap (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n)) :
    (KF n (List.ofFn d)) →ₗ[ℂ] (KF n (List.ofFn fun k => d (σ.symm k))) :=
  LinearMap.codRestrict _ (permFunctionLinear d σ) (permFunction_mem_kFinite d σ)

theorem permKMap_coe (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n))
    (f : KF n (List.ofFn d)) :
    ((permKMap d σ f : KF n (List.ofFn fun k => d (σ.symm k))) :
      Langlands.GeneralLinear n ℂ → ℂ) = permFunction d σ f :=
  rfl

/-- `f ↦ F_f` is `U(n)`-equivariant. -/
theorem permKMap_equivariant (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n))
    (k : Matrix.unitaryGroup (Fin n) ℂ) (f : KF n (List.ofFn d)) :
    permKMap d σ (complexStandardRep n (List.ofFn d) k f) =
      complexStandardRep n (List.ofFn fun k => d (σ.symm k)) k (permKMap d σ f) := by
  apply Subtype.ext
  rw [permKMap_coe, principalSeriesRep_apply_coe, permKMap_coe,
    permFunction_rightTranslation]

/-- `f ↦ F_f` is injective: `F_f(P⁻¹ κ) = f(κ)` for unitary `κ`. -/
theorem permKMap_injective (d : Fin n → ComplexCharacterData) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permKMap d σ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro f hf
  rw [LinearMap.mem_ker] at hf
  rw [Submodule.mem_bot]
  apply kFiniteEval_one_separating
  intro κ
  have h0 := congrArg (fun F : KF n (List.ofFn fun k => d (σ.symm k)) =>
    (F : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits (star (permUnitary σ) * κ))) hf
  simp only [permKMap_coe, Submodule.coe_zero, Pi.zero_apply] at h0
  rw [permFunction, frobeniusFunction_eq (isTorusEigenfunctional_evalPerm d σ) _ f _
    (star (permUnitary σ) * κ) Matrix.blockTriangular_one isUnit_one (by
      rw [Matrix.one_mul]; rfl), borelChar_one, one_mul] at h0
  rw [kFiniteEval_apply, complexStandardRep_apply_apply, one_mul]
  rw [evalPerm, kFiniteEval_apply, complexStandardRep_apply_apply, ← map_mul, ← mul_assoc,
    Unitary.mul_star_self (permUnitary σ), one_mul] at h0
  exact h0

end Langlands.Archimedean.ComplexPermutation
