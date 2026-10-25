import Langlands.Representation.Whittaker.AsymptoticStatement

/-!
# Whittaker torus expansion with last diagonal entry one

The last-entry-one case of JPS (1979), Proposition (2.2), with the finite-type
extension of Remark (2.2.5). The telescope and the full-torus finite-function
predicate agree with `WhittakerTypeAsymptoticStatement`. The expansion is
required only when the last diagonal entry is one. This is a proposition
definition, not a proof.
-/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- JPS (1979), Proposition (2.2) and Remark (2.2.5): for an admissible
finite-type representation with a one-dimensional nonzero space of Whittaker
functionals, choose a finite set of finite functions on the full diagonal
torus uniformly before the functional and vector. Every resulting Whittaker
function has a Schwartz--Bruhat expansion on the last-entry-one subtorus.

Full-torus functions are a derived packaging: pull back the source's finite
functions on the simple-root torus along the simple-root homomorphism. -/
def WhittakerLastEntryOneAsymptoticStatement : Prop :=
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
            ∀ a, a (Fin.last n) = 1 →
              ℓ (ρ (torus a) v) = ∑ χ ∈ X, φ χ (roots a) * χ a

end Langlands
