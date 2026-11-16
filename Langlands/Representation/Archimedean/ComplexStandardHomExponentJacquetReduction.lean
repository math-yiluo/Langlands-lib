import Langlands.Representation.Archimedean.ComplexStandardHomExponent
import Langlands.Representation.Archimedean.ComplexStandardSurjectionInjectiveReduction
import Langlands.Representation.Archimedean.ComplexSwapJacquetFunctional
import Langlands.Representation.Archimedean.ComplexSwapJacquetLie
import Langlands.Representation.Archimedean.ComplexPermutationKType

/-!
# Exponent shape of intertwinings from the exponents of Jacquet functionals

`ComplexStandardJacquetExponentStatement` (JE) describes the exponents of the nonzero Jacquet
functionals on the `U(n)`-finite principal series `X(d)` of `GL_n(ℂ)`: in the coordinates
`p = t + l/2`, `q = t - l/2` of the characters, they are those of `d` permuted by one
permutation `σ` and shifted by nonnegative integer combinations `u`, `v` of the simple roots.

`ComplexStandardHomExponentJacquetReductionStatement` says that JE implies the Library's
`ComplexStandardHomExponentStatement` (E). The theorem
`complexStandardHomExponentJacquetReduction` proves it: a nonzero intertwining map
`T : X(d) → X(c)` gives the nonzero Jacquet functional `ℓ(f) = (T f)(1)` on `X(d)`, whose
exponents are those of `c`.

This module does not prove JE or E; JE is the premise of the reduction.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

/-- Exponents of Jacquet functionals of complex principal series. Let
`d : Fin n → ComplexCharacterData` and let `ℓ ≠ 0` be a Jacquet functional on the `U(n)`-finite
functions of the standard module of `d`, with exponents `a`, `b` (`IsComplexJacquetFunctional`).
Then there are a permutation `σ` of `Fin n` and integer vectors `u`, `v`, each a nonnegative
integer combination of the simple roots `e_i - e_{i+1}`, such that for every `j`
`a_j = 2 t(d_{σ j}) + (n - 1) - 2j + (u_j + v_j)` and `b_j = i (l(d_{σ j}) + u_j - v_j)`
(`t` = `exponent`, `l` = `weight`). -/
def ComplexStandardJacquetExponentStatement : Prop :=
  ∀ (n : ℕ) (d : Fin n → ComplexCharacterData)
    (ℓ : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ)
    (a b : Fin n → ℂ),
    ℓ ≠ 0 → IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn d)) ℓ a b →
      ∃ (σ : Equiv.Perm (Fin n)) (u v : Fin n → ℤ),
        IsNonnegSimpleRootCombination u ∧ IsNonnegSimpleRootCombination v ∧
          ∀ j : Fin n,
            a j = 2 * (d (σ j)).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ) +
                ((u j + v j : ℤ) : ℂ) ∧
              b j = Complex.I * (((d (σ j)).weight : ℂ) + ((u j - v j : ℤ) : ℂ))

/-- The exponents of Jacquet functionals of complex principal series give the exponent shape of
intertwinings between complex principal series. -/
def ComplexStandardHomExponentJacquetReductionStatement : Prop :=
  ComplexStandardJacquetExponentStatement → ComplexStandardHomExponentStatement

namespace ComplexStandardHomExponentJacquet

variable {n : ℕ}

/-- Evaluation at the identity is a Jacquet functional on the `U(n)`-finite functions of the
standard module of `c`, with the exponents `2 t(c_j) + (n - 1) - 2j` and `i l(c_j)`. -/
theorem isComplexJacquetFunctional_kFiniteEval_one (c : Fin n → ComplexCharacterData) :
    IsComplexJacquetFunctional n (complexStandardLie n (List.ofFn c))
      (kFiniteEval (complexStandardModule n (List.ofFn c)) 1)
      (fun j => 2 * (c j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ))
      (fun j => Complex.I * ((c j).weight : ℂ)) := by
  have hn : (List.ofFn c).length = n := List.length_ofFn
  refine ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · rw [kFiniteEval_apply, ComplexSwapJacquet.coe_lie]
    exact ComplexSwapJacquet.rightDerivative_one_strictUpper
      (ComplexSwapJacquet.mem_of_mem_kFs v.2) X
      (fun a b hba => hX a b (Fin.le_iff_val_le_val.mp hba))
  · rw [kFiniteEval_apply, kFiniteEval_apply, ComplexSwapJacquet.coe_lie,
      ComplexSwapJacquet.rightDerivative_one_diag hn (ComplexSwapJacquet.mem_of_mem_kFs v.2),
      ComplexSwapJacquet.kappa_one]
    simp
  · rw [kFiniteEval_apply, kFiniteEval_apply, ComplexSwapJacquet.coe_lie,
      ComplexSwapJacquet.rightDerivative_one_diag hn (ComplexSwapJacquet.mem_of_mem_kFs v.2),
      ComplexSwapJacquet.kappa_I]
    simp

/-- An intertwining map composed with a Jacquet functional on its target is a Jacquet
functional on its source, with the same exponents. -/
theorem isComplexJacquetFunctional_comp {d c : List ComplexCharacterData}
    {T : kFiniteFunctions (complexStandardModule n d) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n c) (unitaryCompact ℂ n)}
    (hT : IsComplexStandardIntertwining n (complexStandardRep n c) (complexStandardLie n c) d T)
    {ℓ : kFiniteFunctions (complexStandardModule n c) (unitaryCompact ℂ n) →ₗ[ℂ] ℂ}
    {a b : Fin n → ℂ} (hℓ : IsComplexJacquetFunctional n (complexStandardLie n c) ℓ a b) :
    IsComplexJacquetFunctional n (complexStandardLie n d) (ℓ.comp T) a b := by
  refine ⟨fun X hX v => ?_, fun j v => ⟨?_, ?_⟩⟩
  · rw [LinearMap.comp_apply, hT.map_lie]
    exact hℓ.1 X hX (T v)
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_lie]
    exact (hℓ.2 j (T v)).1
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.map_lie]
    exact (hℓ.2 j (T v)).2

/-- A nonzero intertwining map stays nonzero after evaluation at the identity, since
evaluation at `1` separates `U(n)`-orbits (`ComplexPermutation.kFiniteEval_one_separating`). -/
theorem kFiniteEval_one_comp_ne_zero {d c : List ComplexCharacterData}
    {T : kFiniteFunctions (complexStandardModule n d) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n c) (unitaryCompact ℂ n)}
    (hT0 : T ≠ 0)
    (hT : IsComplexStandardIntertwining n (complexStandardRep n c) (complexStandardLie n c) d
      T) :
    (kFiniteEval (complexStandardModule n c) 1).comp T ≠ 0 := by
  intro h
  apply hT0
  ext f : 1
  refine ComplexPermutation.kFiniteEval_one_separating c (T f) fun k => ?_
  rw [← hT.map_rep, ← LinearMap.comp_apply, h, LinearMap.zero_apply]

end ComplexStandardHomExponentJacquet

open ComplexStandardHomExponentJacquet in
/-- Proof of the reduction. For a nonzero intertwining map `T : X(d) → X(c)`, the functional
`ℓ(f) = (T f)(1)` is nonzero (`kFiniteEval_one_comp_ne_zero`) and is a Jacquet functional with
the exponents `a_j = 2 t(c_j) + (n - 1) - 2j`, `b_j = i l(c_j)` of `c`
(`isComplexJacquetFunctional_kFiniteEval_one`, `isComplexJacquetFunctional_comp`). JE gives `σ`,
`u`, `v` with `a_j = 2 t(d_{σ j}) + (n - 1) - 2j + (u_j + v_j)` and
`b_j = i (l(d_{σ j}) + u_j - v_j)`; comparing gives E. -/
theorem complexStandardHomExponentJacquetReduction :
    ComplexStandardHomExponentJacquetReductionStatement := by
  intro hJE n d c T hT0 hT
  obtain ⟨σ, u, v, hu, hv, hj⟩ :=
    hJE n d ((kFiniteEval (complexStandardModule n (List.ofFn c)) 1).comp T) _ _
      (kFiniteEval_one_comp_ne_zero hT0 hT)
      (isComplexJacquetFunctional_comp hT (isComplexJacquetFunctional_kFiniteEval_one c))
  refine ⟨σ, u, v, hu, hv, fun j => ⟨?_, ?_⟩⟩
  · have h := (hj j).1
    linear_combination h / 2
  · have h := (hj j).2
    have h' : ((c j).weight : ℂ) = ((d (σ j)).weight : ℂ) + ((u j - v j : ℤ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero h
    exact_mod_cast h'

end Langlands.Archimedean
