import Langlands.Representation.Archimedean.RealKTypeTransport

/-!
# Extending a compact coefficient model into a real standard module

Evaluation at the identity identifies the possible compact intertwiners out of a
finite-dimensional model with its linear forms satisfying the standard module's sign and
Fourier conditions, when the coefficients of the forms are continuous.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCompactWitnessExtension

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula PrincipalSeriesExtension
  RealBlockFourierFinite

local notation "O(" n ")" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Std(" n ", " ds ")" => kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

variable {n : ℕ} {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- The block rotation as an element of the orthogonal group. -/
def compactBlockRotation (n p : ℕ) (θ : ℝ) : O(n) :=
  ⟨(blockRotation n p θ : Matrix (Fin n) (Fin n) ℝ), blockRotation_mem_unitaryCompact n p θ⟩

@[simp]
theorem compactBlockRotation_toUnits (n p : ℕ) (θ : ℝ) :
    Unitary.toUnits (compactBlockRotation n p θ) = blockRotation n p θ :=
  Units.ext rfl

/-- The conditions on a linear form for its coefficients to have standard module symmetry. -/
def IsStandardFunctional (ds : List RealBlock) (ρ : Representation ℂ (O(n)) D)
    (ℓ : D →ₗ[ℂ] ℂ) : Prop :=
  (∀ (a : Fin n → ℝˣ) (x : D),
    ℓ (ρ (signDiagonal (fun i => (a i : ℝ))) x) =
      principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) * ℓ x) ∧
  ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d →
    ∀ j : ℤ, |j| < |d.weight| → ∀ x : D,
      coeff j (fun θ => ℓ (ρ (compactBlockRotation n p θ) x)) = 0

variable (ρ : Representation ℂ (O(n)) D) (ℓ : D →ₗ[ℂ] ℂ)

/-- Taking the compact coefficient of a vector against a fixed linear form. -/
def coefficientMap : D →ₗ[ℂ] (O(n) → ℂ) where
  toFun x k := ℓ (ρ k x)
  map_add' x y := funext fun k => by simp
  map_smul' c x := funext fun k => by simp

private theorem coefficientMap_mul (x : D) (k κ : O(n)) :
    coefficientMap ρ ℓ x (κ * k) = coefficientMap ρ ℓ (ρ k x) κ := by
  change ℓ (ρ (κ * k) x) = ℓ (ρ κ (ρ k x))
  rw [map_mul]
  rfl

private theorem finiteDimensional_translates [FiniteDimensional ℂ D] (x : D) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : O(n) =>
      fun κ => coefficientMap ρ ℓ x (κ * k))) := by
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (coefficientMap ρ ℓ))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact ⟨ρ k x, funext fun κ => (coefficientMap_mul ρ ℓ x k κ).symm⟩

variable {ds : List RealBlock}

private theorem extension_mem_standard [FiniteDimensional ℂ D] (hN : realRank ds = n)
    (hℓ : IsStandardFunctional ds ρ ℓ) (x : D) (hc : Continuous (coefficientMap ρ ℓ x)) :
    extension (shiftedExponent n (realPositionExponent ds)) (coefficientMap ρ ℓ x) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) := by
  have hf := extension_mem_kFiniteFunctions (realPositionExponent ds)
    (realPositionCharacter_eq_signUnit_mul ds) hc (finiteDimensional_translates ρ ℓ x)
    (fun a k => by
      rw [coefficientMap_mul]
      exact hℓ.1 a (ρ k x))
  refine ⟨RealKTypeTransport.mem_realStandardModule_of_unitaryCompact hN hf.1 ?_, hf.2⟩
  intro p d hd j hj k hk
  let κ : O(n) := ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩
  rw [blockFourierCoefficient_eq_coeff]
  convert hℓ.2 p d hd j hj (ρ κ x) using 1
  apply congrArg (coeff j)
  funext θ
  have hprod : Unitary.toUnits (compactBlockRotation n p θ * κ) = blockRotation n p θ * k := by
    rw [map_mul, compactBlockRotation_toUnits, RealKTypeCount.toUnits_mk hk]
  rw [← hprod, extension_unitary, coefficientMap_mul]
  rfl

private theorem ext_of_compact {f g : Std(n, ds)}
    (h : ∀ k : O(n), f.val (Unitary.toUnits k) = g.val (Unitary.toUnits k)) : f = g :=
  RealKTypeCount.restrict_injective (realStandardModule_le_principalSeries n ds) (funext h)

private theorem compact_action_eval (k κ : O(n)) (f : Std(n, ds)) :
    (realStandardRep n ds k f).val (Unitary.toUnits κ) = f.val (Unitary.toUnits (κ * k)) := by
  change f.val (Unitary.toUnits κ * Unitary.toUnits k) = _
  rw [map_mul]

private theorem compact_action_eval_one (k : O(n)) (f : Std(n, ds)) :
    (realStandardRep n ds k f).val 1 = f.val (Unitary.toUnits k) := by
  simpa only [map_one, one_mul] using compact_action_eval k 1 f

private theorem signDiagonal_toUnits (a : Fin n → ℝˣ) :
    Unitary.toUnits (signDiagonal (fun i => (a i : ℝ))) =
      Iwasawa.diagonalUnits (fun i => signUnit (a i)) := by
  apply Units.ext
  change Matrix.diagonal (fun i => signReal (a i)) =
    Matrix.diagonal (fun i => (signUnit (a i) : ℝ))
  simp only [signUnit_val]

/-- Evaluation at the identity of a compact intertwiner satisfies the left
sign equations and the block Fourier cutoff. -/
theorem evaluation_isStandardFunctional (A : D →ₗ[ℂ] Std(n, ds))
    (hA : ∀ k x, A (ρ k x) = realStandardRep n ds k (A x)) :
    IsStandardFunctional ds ρ ((kFiniteEval (realStandardModule n ds) 1).comp A) := by
  constructor
  · intro a x
    simp only [LinearMap.comp_apply, kFiniteEval_apply, hA, compact_action_eval_one,
      signDiagonal_toUnits]
    simpa only [Subgroup.coe_one, mul_one] using
      (A x).2.1.1.2 (fun i => signUnit (a i)) 1 1
  · intro p d hd j hj x
    simp only [LinearMap.comp_apply, kFiniteEval_apply, hA, compact_action_eval_one,
      compactBlockRotation_toUnits]
    simpa only [blockFourierCoefficient_eq_coeff, mul_one] using (A x).2.1.2 p d hd j hj 1

/-- Equality of compact intertwiners can be checked by evaluation at the identity. -/
theorem compactIntertwiner_ext {A B : D →ₗ[ℂ] Std(n, ds)}
    (hA : ∀ k x, A (ρ k x) = realStandardRep n ds k (A x))
    (hB : ∀ k x, B (ρ k x) = realStandardRep n ds k (B x))
    (h : (kFiniteEval (realStandardModule n ds) 1).comp A =
      (kFiniteEval (realStandardModule n ds) 1).comp B) :
    A = B := by
  apply LinearMap.ext
  intro x
  apply ext_of_compact
  intro k
  have he := DFunLike.congr_fun h (ρ k x)
  simpa only [LinearMap.comp_apply, kFiniteEval_apply, hA, hB, compact_action_eval_one] using he

/-- A one-dimensional space of qualifying linear forms with a nonzero continuous
coefficient model supplies a vector scaled by all compact-equivariant endomorphisms. -/
theorem exists_scalarVector_of_compactCoefficients [FiniteDimensional ℂ D]
    (hN : realRank ds = n) (hℓ : IsStandardFunctional ds ρ ℓ) (hne : ℓ ≠ 0)
    (hc : ∀ x, Continuous (coefficientMap ρ ℓ x))
    (hline : ∀ ℓ' : D →ₗ[ℂ] ℂ, IsStandardFunctional ds ρ ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) :
    ∃ f : Std(n, ds), f ≠ 0 ∧
      ∀ E : Module.End ℂ (Std(n, ds)),
        (∀ k x, E (realStandardRep n ds k x) = realStandardRep n ds k (E x)) →
        ∃ c : ℂ, E f = c • f := by
  let L := (extensionLinear (shiftedExponent n (realPositionExponent ds))).comp (coefficientMap ρ ℓ)
  let A : D →ₗ[ℂ] Std(n, ds) :=
    L.codRestrict _ fun x => extension_mem_standard ρ ℓ hN hℓ x (hc x)
  have hEval (x : D) (k : O(n)) : (A x).val (Unitary.toUnits k) = ℓ (ρ k x) :=
    extension_unitary _ _ _
  have hA (k : O(n)) (x : D) : A (ρ k x) = realStandardRep n ds k (A x) := by
    apply ext_of_compact
    intro κ
    rw [compact_action_eval, hEval, hEval, map_mul]
    rfl
  obtain ⟨x, hx⟩ : ∃ x : D, ℓ x ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun y => h y)
  have hxA : A x ≠ 0 := by
    intro h
    have he := hEval x 1
    simp only [h, map_one, Module.End.one_apply, Submodule.coe_zero, Pi.zero_apply] at he
    exact hx he.symm
  refine ⟨A x, hxA, fun E hE => ?_⟩
  have hB (k : O(n)) (y : D) :
      (E.comp A) (ρ k y) = realStandardRep n ds k ((E.comp A) y) := by
    simp only [LinearMap.comp_apply, hA, hE]
  obtain ⟨c, h⟩ := hline _ (evaluation_isStandardFunctional ρ (E.comp A) hB)
  refine ⟨c, ext_of_compact ?_⟩
  intro k
  have he := DFunLike.congr_fun h (ρ k x)
  simp only [LinearMap.comp_apply, kFiniteEval_apply, hA, hE, compact_action_eval_one,
    LinearMap.smul_apply, smul_eq_mul] at he
  change (E (A x)).val (Unitary.toUnits k) = c * (A x).val (Unitary.toUnits k)
  rwa [hEval]

end Langlands.Archimedean.RealCompactWitnessExtension
