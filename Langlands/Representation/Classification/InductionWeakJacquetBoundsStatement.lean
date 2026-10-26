import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Geometric.RefinementFunctors

/-!
# Preservation of weak upper Jacquet bounds by actual normalized induction

This algebraic proposition carries bounds for all upper refined generalized
exponents of an actual product-Levi representation to all standard upper
Jacquet exponents of its actual normalized parabolic induction.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Actual normalized induction preserves the weak upper generalized-exponent
bounds. Its premise tests every source refinement on its within-block chamber;
its conclusion tests every ambient standard Jacquet module. -/
def GLInductionWeakJacquetBoundsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (B.Levi F.Carrier) V),
      Representation.IsIrreducible σ → IsAdmissible σ →
      (∀ (D : BlockRefinement B)
        (ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (B.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet B D σ).comp
            ((flattenedLeviEquiv F.Carrier B D).toMonoidHom.comp
              ((B.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (B.flatten D).length → F.Carrierˣ,
          (∀ j : Fin B.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (B.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ a : ℂ)‖ ≤ 1) →
      ∀ (C : BlockShape n) (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
        T.IsJacquetExponent C (T.normalizedParabolicInduced B σ) χ →
        ∀ a : Fin C.length → F.Carrierˣ,
          Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
          ‖(χ a : ℂ)‖ ≤ 1

end Langlands
