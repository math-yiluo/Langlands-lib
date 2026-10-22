import Langlands.Group.GL.Basic
import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Canonical
import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible

/-!
# Gauge bounds and torus expansions of Whittaker functions

Proposition targets for JPSS (1983), Section 2.5, printed pages 388-389,
which recalls JPS, *Automorphic forms on GL(3) I* (1979), Section 2,
Proposition (2.2), Remark (2.2.5) and the gauges of (2.3). The diagonal
torus is parameterized by families of units and its simple-root coordinates are
`a i / a (i + 1)`. None of the propositions is asserted to be proved.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- JPSS (2.5): for a representation of Whittaker type whose central character
is unitary, every Whittaker function `g ↦ ℓ (ρ g v)` is majorized by a gauge.

A gauge is left invariant under upper unitriangular matrices, right invariant
under the matrices with integral entries and integral inverse, and equals
`‖φ (α a)‖ * |α₁(a) ⋯ αₙ(a)| ^ (-t)` on the diagonal torus, where `α` are the
simple-root coordinates, `t ≥ 0` and `φ` is a Schwartz--Bruhat function. -/
def WhittakerGaugeStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) ρ.asModule →
      (∃ ω : F.Carrierˣ → ℂ, (∀ z, ‖ω z‖ = 1) ∧
        ∀ z v, ρ (GeneralLinear.scalar z) v = ω z • v) →
      let unipotent := fun g : GeneralLinear (n + 1) F.Carrier =>
        (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1
      let θ := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∏ i : Fin n, ψ (g.val i.castSucc i.succ)
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let integral := fun g : GeneralLinear (n + 1) F.Carrier =>
        (∀ i j, g.val i j ∈ F.canonicalTopologicalData.Integers) ∧
        ∀ i j, (g⁻¹).val i j ∈ F.canonicalTopologicalData.Integers
      let torus : (Fin (n + 1) → F.Carrierˣ) →* GeneralLinear (n + 1) F.Carrier :=
        (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F.Carrier).toMonoidHom).comp
          MulEquiv.piUnits.symm.toMonoidHom
      let roots := fun (a : Fin (n + 1) → F.Carrierˣ) (i : Fin n) =>
        ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
      let gauge := fun ξ : GeneralLinear (n + 1) F.Carrier → ℝ =>
        (∀ u g, unipotent u → ξ (u * g) = ξ g) ∧
        (∀ g k, integral k → ξ (g * k) = ξ g) ∧
        ∃ (t : ℝ) (φ : HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier)), 0 ≤ t ∧
          ∀ a, ξ (torus a) =
            ‖φ (roots a)‖ *
              F.canonicalTopologicalData.normalizedAbs (∏ i, roots a i) ^ (-t)
      ∀ ℓ : Module.Dual ℂ V, ℓ ≠ 0 → equivariant ℓ →
        (∀ ℓ' : Module.Dual ℂ V, equivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) →
        ∀ v : V, ∃ ξ, gauge ξ ∧ ∀ g, ‖ℓ (ρ g v)‖ ≤ ξ g

/-- JPS (1979), Proposition (2.2) with Remark (2.2.5), for the Whittaker
functions of a representation of Whittaker type in the sense of JPSS (2.1):
there is a finite set `X` of finite functions on the diagonal torus, depending
only on the representation, such that on the torus every Whittaker function is
`∑ χ ∈ X, φ_χ (α a) * χ a` with Schwartz--Bruhat functions `φ_χ`.

A finite function is a continuous function whose translates span a
finite-dimensional space. -/
def WhittakerTypeAsymptoticStatement : Prop :=
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
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let torus : (Fin (n + 1) → F.Carrierˣ) →* GeneralLinear (n + 1) F.Carrier :=
        (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F.Carrier).toMonoidHom).comp
          MulEquiv.piUnits.symm.toMonoidHom
      let roots := fun (a : Fin (n + 1) → F.Carrierˣ) (i : Fin n) =>
        ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
      let finiteFunction := fun χ : (Fin (n + 1) → F.Carrierˣ) → ℂ =>
        Continuous χ ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : Fin (n + 1) → F.Carrierˣ => fun a => χ (b * a)))
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ℓ ∧
        ∀ ℓ' : Module.Dual ℂ V, equivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) →
      ∃ X : Finset ((Fin (n + 1) → F.Carrierˣ) → ℂ), (∀ χ ∈ X, finiteFunction χ) ∧
        ∀ ℓ : Module.Dual ℂ V, equivariant ℓ → ∀ v : V,
          ∃ φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) →
              HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
            ∀ a, ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a

/-- JPSS (2.5), display (2), citing JPS (1979), Proposition (2.2): the same
torus expansion for an irreducible admissible generic representation, that is,
one with a nonzero Whittaker functional. -/
def GenericWhittakerAsymptoticStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
      (ψ : AddChar F.Carrier ℂ),
      Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ → Representation.IsIrreducible ρ →
      let unipotent := fun g : GeneralLinear (n + 1) F.Carrier =>
        (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1
      let θ := fun g : GeneralLinear (n + 1) F.Carrier =>
        ∏ i : Fin n, ψ (g.val i.castSucc i.succ)
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let torus : (Fin (n + 1) → F.Carrierˣ) →* GeneralLinear (n + 1) F.Carrier :=
        (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F.Carrier).toMonoidHom).comp
          MulEquiv.piUnits.symm.toMonoidHom
      let roots := fun (a : Fin (n + 1) → F.Carrierˣ) (i : Fin n) =>
        ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)
      let finiteFunction := fun χ : (Fin (n + 1) → F.Carrierˣ) → ℂ =>
        Continuous χ ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : Fin (n + 1) → F.Carrierˣ => fun a => χ (b * a)))
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ℓ) →
      ∃ X : Finset ((Fin (n + 1) → F.Carrierˣ) → ℂ), (∀ χ ∈ X, finiteFunction χ) ∧
        ∀ ℓ : Module.Dual ℂ V, equivariant ℓ → ∀ v : V,
          ∃ φ : ((Fin (n + 1) → F.Carrierˣ) → ℂ) →
              HarmonicAnalysis.SchwartzBruhat (Fin n → F.Carrier),
            ∀ a, ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a

/-- The three Whittaker-function estimates, with the same independent universes. -/
def WhittakerAsymptoticPrerequisitesStatement : Prop :=
  WhittakerGaugeStatement.{uF, uV} ∧ WhittakerTypeAsymptoticStatement.{uF, uV} ∧
    GenericWhittakerAsymptoticStatement.{uF, uV}

end Langlands
