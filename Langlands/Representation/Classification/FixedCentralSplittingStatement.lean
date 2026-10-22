import Langlands.LocalField.Definitions
import Langlands.Representation.Exponents.Central
import Langlands.Representation.MatrixCoefficient.Definitions
import Langlands.Representation.Smooth.Contragredient.Definitions
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-!
# Splitting with a fixed scalar central character

The coefficient-support condition is an actual compactness predicate on the
central quotient. The two splitting assertions are proposition definitions,
not Lean proofs of Casselman's projectivity and injectivity theorem.
-/

namespace Langlands

universe uG uV uF uU uW

/-- Each smooth-dual coefficient has support contained in the inverse image
of some compact subset of the actual central quotient. The compact set may
depend on both the vector and the smooth functional. -/
def HasCompactSmoothCoefficientsModCenter
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Prop :=
  ∀ (ℓ : SmoothDual ρ) (v : V),
    ∃ C : Set (G ⧸ Subgroup.center G), IsCompact C ∧
      ∀ g : G, matrixCoefficient ρ ℓ v g ≠ 0 →
        QuotientGroup.mk g ∈ C

/-- GL_n specialization of Casselman 1995, Theorems 5.3.1 and 5.4.1:
an admissible representation with compact smooth coefficients modulo the
center splits every surjection onto it and every injection from it within
the smooth category with the same prescribed scalar central character. -/
def GLFixedCentralCharacterSplittingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopology
    ∀ (n : ℕ), 0 < n →
      let G := Matrix.GeneralLinearGroup (Fin n) F.Carrier
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V) (χ : Subgroup.center G →* ℂˣ),
        IsOpen (χ.ker : Set (Subgroup.center G)) →
        IsAdmissible ρ →
        centralCharacterSpace ρ χ 1 = ⊤ →
        HasCompactSmoothCoefficientsModCenter ρ →
        (∀ (U : Type uU) [AddCommGroup U] [Module ℂ U]
          (σ : Representation ℂ G U),
          IsSmooth σ →
          centralCharacterSpace σ χ 1 = ⊤ →
          ∀ f : Representation.IntertwiningMap σ ρ,
            Function.Surjective f →
            ∃ s : Representation.IntertwiningMap ρ σ,
              f.comp s = Representation.IntertwiningMap.id ρ) ∧
        (∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
          (τ : Representation ℂ G W),
          IsSmooth τ →
          centralCharacterSpace τ χ 1 = ⊤ →
          ∀ j : Representation.IntertwiningMap ρ τ,
            Function.Injective j →
            ∃ r : Representation.IntertwiningMap τ ρ,
              r.comp j = Representation.IntertwiningMap.id ρ)

end Langlands
