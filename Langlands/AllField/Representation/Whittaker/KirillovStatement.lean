import Langlands.Representation.Whittaker.KirillovStatement
import Langlands.AllField.Group.GL.Padic
/-!
# Kirillov-model prerequisites for the JPSS integral theory

Proposition targets for the restriction of Whittaker functions to the actual
mirabolic matrices of `GL_{n+1}(F)`. JPSS (1983), Section 2.2, printed page 386;
Bernstein--Zelevinsky (1976), 5.15-5.19, printed pages 49-50.
Neither proposition is asserted to be proved by these definitions.
-/

namespace Langlands.AllField

open scoped BigOperators

universe uF uV

/-- JPSS (2.2): for an admissible representation of finite type whose space of
Whittaker functionals is one-dimensional, every smooth left `(N, θ)`-covariant
function on the mirabolic subgroup with compact support modulo `N` is the
restriction of a Whittaker function.

The upper-unitriangular, mirabolic, covariance, smoothness and support
conditions are spelled out on actual matrices; nothing is parameterized by an
arbitrary predicate. -/
def WhittakerTypeKirillovStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
      (ψ : AddChar F ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F)) ρ.asModule →
      let unipotent := fun g : GeneralLinear (n + 1) F =>
        (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1
      let θ := fun g : GeneralLinear (n + 1) F =>
        ∏ i : Fin n, ψ (g.val i.castSucc i.succ)
      let mirabolic := fun g : GeneralLinear (n + 1) F =>
        ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let kirillov := fun φ : GeneralLinear (n + 1) F → ℂ =>
        (∀ u q, unipotent u → mirabolic q → φ (u * q) = θ u * φ q) ∧
        (∃ K : OpenSubgroup (GeneralLinear (n + 1) F),
          ∀ q k, mirabolic q → mirabolic k → k ∈ K → φ (q * k) = φ q) ∧
        (∃ C : Set (GeneralLinear (n + 1) F), IsCompact C ∧
          ∀ q, mirabolic q → φ q ≠ 0 → ∃ u c, unipotent u ∧ c ∈ C ∧ q = u * c)
      ∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 → equivariant ℓ →
        (∀ ℓ' : Module.Dual ℂ V, equivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) →
        ∀ φ, kirillov φ → ∃ v : V, ∀ q, mirabolic q → ℓ (ρ q v) = φ q

end Langlands.AllField
