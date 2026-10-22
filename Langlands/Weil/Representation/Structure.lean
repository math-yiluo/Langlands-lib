import Langlands.Representation.Twist.Definitions
import Langlands.Weil.Pullback
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Finite-image and unramified reductions of complex Weil representations

The integer-extension statement isolates the group-theoretic setting of
Tate 2.2.1. The extension statement uses the accepted explicit pullback from
a compact Hausdorff nonarchimedean group, not an arbitrary dense homomorphism.
-/

namespace Langlands.Weil

universe uW uV

/-- General commuting unramified correction, irreducible scalar correction,
and the finite-order determinant criterion for irreducibles. -/
def UnramifiedReduction : Prop :=
  ∀ (W : Type uW) [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
    (d : W →* Degree) [CompactSpace d.ker] [NonarchimedeanGroup d.ker],
    Function.Surjective d → IsOpen (d.ker : Set W) →
    ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : Representation ℂ W V),
      Continuous (fun w : W => (ρ w).toContinuousLinearMap) →
      (∃ τ σ : Representation ℂ W V,
        Continuous (fun w : W => (τ w).toContinuousLinearMap) ∧
        (∀ i : d.ker, τ (i : W) = 1) ∧
        (∀ w w' : W, Commute (ρ w) (τ w')) ∧
        (∀ w : W, σ w = ρ w * τ w) ∧
        Continuous (fun w : W => (σ w).toContinuousLinearMap) ∧
        (Set.range σ).Finite) ∧
      (Representation.IsIrreducible ρ →
        (∃ (χ : W →* ℂˣ) (σ : Representation ℂ W V),
          Continuous χ ∧
          (∀ i : d.ker, χ (i : W) = 1) ∧
          Continuous (fun w : W => (σ w).toContinuousLinearMap) ∧
          (Set.range σ).Finite ∧ Representation.IsIrreducible σ ∧
          ρ = Langlands.twist χ σ) ∧
        ((Set.range ρ).Finite ↔
          ∃ n : ℕ, 0 < n ∧ ∀ w : W, LinearMap.det (ρ w) ^ n = 1))

/-- A finite-image continuous representation of the explicit pullback extends
uniquely to its profinite ambient group, and only such representations extend. -/
def FiniteImageExtension : Prop :=
  ∀ (Γ : Type uW) [Group Γ] [TopologicalSpace Γ]
    [NonarchimedeanGroup Γ] [CompactSpace Γ] [T2Space Γ]
    (φ : Γ →ₜ* ProfiniteIntegers), Function.Surjective φ →
    ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V]
      [FiniteDimensional ℂ V] (ρ : Representation ℂ (Pullback φ) V),
      Continuous (fun w : Pullback φ => (ρ w).toContinuousLinearMap) →
      ((Set.range ρ).Finite ↔
        ∃! σ : Representation ℂ Γ V,
          Continuous (fun g : Γ => (σ g).toContinuousLinearMap) ∧
          σ.comp (projection φ).toMonoidHom = ρ)

/-- The complete finite-image and unramified-reduction statement family. -/
def RepresentationStructure : Prop :=
  UnramifiedReduction.{uW, uV} ∧ FiniteImageExtension.{uW, uV}

end Langlands.Weil
