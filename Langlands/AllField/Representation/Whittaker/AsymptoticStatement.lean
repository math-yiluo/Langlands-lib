import Langlands.Representation.Whittaker.AsymptoticStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Gauge bounds and torus expansions of Whittaker functions

Proposition targets for JPSS (1983), Section 2.5, printed pages 388-389,
which recalls JPS, *Automorphic forms on GL(3) I* (1979), Section 2,
Proposition (2.2), Remark (2.2.5) and the gauges of (2.3). The diagonal
torus is parameterized by families of units and its simple-root coordinates are
`a i / a (i + 1)`. None of the propositions is asserted to be proved.
-/

namespace Langlands.AllField

open scoped BigOperators

universe uF uV

/-- JPS (1979), Proposition (2.2) with Remark (2.2.5), for the Whittaker
functions of a representation of Whittaker type in the sense of JPSS (2.1):
there is a finite set `X` of finite functions on the diagonal torus, depending
only on the representation, such that on the torus every Whittaker function is
`∑ χ ∈ X, φ_χ (α a) * χ a` with Schwartz--Bruhat functions `φ_χ`.

A finite function is a continuous function whose translates span a
finite-dimensional space. -/
def WhittakerTypeAsymptoticStatement : Prop :=
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
      let equivariant := fun ℓ : Module.Dual ℂ V =>
        ∀ g, unipotent g → ∀ v, ℓ (ρ g v) = θ g * ℓ v
      let torus : (Fin (n + 1) → Fˣ) →* GeneralLinear (n + 1) F :=
        (Units.map (Matrix.diagonalRingHom (Fin (n + 1)) F).toMonoidHom).comp
          MulEquiv.piUnits.symm.toMonoidHom
      let roots := fun (a : Fin (n + 1) → Fˣ) (i : Fin n) =>
        ((a i.castSucc / a i.succ : Fˣ) : F)
      let finiteFunction := fun χ : (Fin (n + 1) → Fˣ) → ℂ =>
        Continuous χ ∧
          FiniteDimensional ℂ (Submodule.span ℂ
            (Set.range fun b : Fin (n + 1) → Fˣ => fun a => χ (b * a)))
      (∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ equivariant ℓ ∧
        ∀ ℓ' : Module.Dual ℂ V, equivariant ℓ' → ∃ c : ℂ, ℓ' = c • ℓ) →
      ∃ X : Finset ((Fin (n + 1) → Fˣ) → ℂ), (∀ χ ∈ X, finiteFunction χ) ∧
        ∀ ℓ : Module.Dual ℂ V, equivariant ℓ → ∀ v : V,
          ∃ φ : ((Fin (n + 1) → Fˣ) → ℂ) →
              HarmonicAnalysis.SchwartzBruhat (Fin n → F),
            ∀ a, ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a

end Langlands.AllField
