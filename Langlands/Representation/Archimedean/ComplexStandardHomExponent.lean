import Langlands.Representation.Archimedean.PrincipalSeriesGKModule

/-!
# Exponent shape of intertwinings between complex principal series

`ComplexStandardHomExponentStatement` says: if there is a nonzero `(𝔤, K)`-intertwining map from
the `U(n)`-finite functions of the principal series of `d = (d₀, …, d_{n-1})` to those of
`c = (c₀, …, c_{n-1})`, then `c` is a permutation of `d` shifted by nonnegative integer
combinations of the simple roots, separately in the holomorphic and antiholomorphic
coordinates of the characters, with one permutation for both coordinates.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

/-- `u : Fin n → ℤ` is a nonnegative integer combination of the simple roots
`e_i - e_{i+1}` of `𝔤𝔩_n`: all its prefix sums are nonnegative and its total is zero. -/
def IsNonnegSimpleRootCombination {n : ℕ} (u : Fin n → ℤ) : Prop :=
  (∀ k : ℕ, 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), u j) ∧ ∑ j, u j = 0

/-- Exponent shape of intertwinings between complex principal series. Let
`d c : Fin n → ComplexCharacterData` and let `T ≠ 0` be an intertwining map from the
`U(n)`-finite functions of the standard module of `d` to those of `c`. Then there are a
permutation `σ` of `Fin n` and integer vectors `u`, `v`, each a nonnegative integer combination
of the simple roots `e_i - e_{i+1}`, with `t(c_j) = t(d_{σ j}) + (u_j + v_j)/2` and
`l(c_j) = l(d_{σ j}) + u_j - v_j` for every `j` (`t` = `exponent`, `l` = `weight`). In the
coordinates `p = t + l/2`, `q = t - l/2` of the character `z ↦ z^p z̄^q`, this reads
`p(c_j) = p(d_{σ j}) + u_j` and `q(c_j) = q(d_{σ j}) + v_j`. -/
def ComplexStandardHomExponentStatement : Prop :=
  ∀ (n : ℕ) (d c : Fin n → ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n (List.ofFn d)) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n (List.ofFn c)) (unitaryCompact ℂ n)),
    T ≠ 0 →
      IsComplexStandardIntertwining n (complexStandardRep n (List.ofFn c))
        (complexStandardLie n (List.ofFn c)) (List.ofFn d) T →
      ∃ (σ : Equiv.Perm (Fin n)) (u v : Fin n → ℤ),
        IsNonnegSimpleRootCombination u ∧ IsNonnegSimpleRootCombination v ∧
          ∀ j : Fin n,
            (c j).exponent = (d (σ j)).exponent + ((u j + v j : ℤ) : ℂ) / 2 ∧
              (c j).weight = (d (σ j)).weight + (u j - v j)

end Langlands.Archimedean
