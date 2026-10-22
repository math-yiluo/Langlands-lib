import Langlands.Representation.Classification.Supercuspidal
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic

/-!
# Kirillov-model prerequisites for the JPSS integral theory

Proposition targets for the restriction of Whittaker functions to the actual
mirabolic matrices of `GL_{n+1}(F)`. JPSS (1983), Section 2.2, printed page 386;
Bernstein--Zelevinsky (1976), 5.15-5.19, printed pages 49-50.
Neither proposition is asserted to be proved by these definitions.
-/

namespace Langlands

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
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) ρ.asModule →
      let unipotent := fun g : GeneralLinear (n + 1) F.Carrier =>
        (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1
      let θ := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∏ i : Fin n, ψ (g.val i.castSucc i.succ)
      let mirabolic := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let kirillov := fun φ : GeneralLinear (n + 1) F.Carrier → ℂ =>
        (∀ u q, unipotent u → mirabolic q → φ (u * q) = θ u * φ q) ∧
        (∃ K : OpenSubgroup (GeneralLinear (n + 1) F.Carrier),
          ∀ q k, mirabolic q → mirabolic k → k ∈ K → φ (q * k) = φ q) ∧
        (∃ C : Set (GeneralLinear (n + 1) F.Carrier), IsCompact C ∧
          ∀ q, mirabolic q → φ q ≠ 0 → ∃ u c, unipotent u ∧ c ∈ C ∧ q = u * c)
      ∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 → equivariant ℓ →
        (∀ ℓ' : Module.Dual ℂ V, equivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) →
        ∀ φ, kirillov φ → ∃ v : V, ∀ q, mirabolic q → ℓ (ρ q v) = φ q

/-- Bernstein--Zelevinsky (1976), 5.18-5.19, with JPSS (2.2): an irreducible
supercuspidal representation has a nonzero Whittaker functional, and for every
such functional restriction to the mirabolic subgroup is a linear bijection onto
the smooth covariant functions with compact support modulo `N`.

Supercuspidality is the published Jacquet-vanishing predicate, which includes
admissibility. The functions are compared only at actual mirabolic matrices. -/
def SupercuspidalKirillovStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      GeneralLinear.IsSupercuspidal ρ → Representation.IsIrreducible ρ →
      let unipotent := fun g : GeneralLinear (n + 1) F.Carrier =>
        (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1
      let θ := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∏ i : Fin n, ψ (g.val i.castSucc i.succ)
      let mirabolic := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let kirillov := fun φ : GeneralLinear (n + 1) F.Carrier → ℂ =>
        (∀ u q, unipotent u → mirabolic q → φ (u * q) = θ u * φ q) ∧
        (∃ K : OpenSubgroup (GeneralLinear (n + 1) F.Carrier),
          ∀ q k, mirabolic q → mirabolic k → k ∈ K → φ (q * k) = φ q) ∧
        (∃ C : Set (GeneralLinear (n + 1) F.Carrier), IsCompact C ∧
          ∀ q, mirabolic q → φ q ≠ 0 → ∃ u c, unipotent u ∧ c ∈ C ∧ q = u * c)
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ℓ) ∧
      ∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 → equivariant ℓ →
        (∀ v : V, kirillov (fun g => ℓ (ρ g v))) ∧
        ∀ φ, kirillov φ → ∃! v : V, ∀ q, mirabolic q → ℓ (ρ q v) = φ q

/-- Both Kirillov-model targets, with the same independent universes. -/
def KirillovPrerequisitesStatement : Prop :=
  WhittakerTypeKirillovStatement.{uF, uV} ∧ SupercuspidalKirillovStatement.{uF, uV}

end Langlands
