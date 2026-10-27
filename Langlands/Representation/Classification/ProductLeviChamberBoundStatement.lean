import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement
import Langlands.Group.GL.CartanQuotientDefinitions

/-!
# Chamber bound for matrix coefficients of a product Levi

Under the upper generalized-exponent hypothesis of
`GLProductLeviTemperedExponentSufficiencyStatement`, every smooth matrix
coefficient of an admissible representation of an actual GL block Levi is
bounded on the normalized antidominant Cartan representatives by a constant
times `δ^(1/2 - η)`, for each `η > 0`, where `δ` is the product over the outer
blocks of the radial upper-Borel modulus `CartanQuotient.delta`.
-/

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV

/-- Upper generalized-exponent bounds on every refinement give, for each smooth
functional `ℓ`, vector `v` and `η > 0`, a constant `c` with
`‖ℓ(ρ(a(lam)) v)‖ ≤ c ∏_j delta(lam_j)^(1/2 - η)` for all blockwise normalized
exponent tuples `lam`, where `a(lam)` has diagonal blocks `diag(ϖ^(lam_j))`. -/
def GLProductLeviChamberCoefficientBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (C : BlockShape n) (S : Rep.{uV} ℂ (C.Levi F.Carrier)),
      IsAdmissible S.ρ →
      (∀ (D : BlockRefinement C) (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ),
        IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedJacquet C D S.ρ).comp
            ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
              ((C.flatten D).blockScalarLevi F.Carrier))) ψ →
        ∀ a : Fin (C.flatten D).length → F.Carrierˣ,
          (∀ j : Fin C.length, Monotone (fun i : Fin (D j).length =>
            T.normalizedAbs (a (C.flattenBlockEquiv D ⟨j, i⟩) : F.Carrier))) →
          ‖(ψ a : ℂ)‖ ≤ 1) →
      ∀ (ℓ : SmoothDual S.ρ) (v : S) (η : ℝ), 0 < η →
        ∃ c : ℝ, ∀ lam : ∀ j : Fin C.length, Fin (C.size j) → ℤ,
          (∀ j, CartanQuotient.Normalized (lam j)) →
          ‖matrixCoefficient S.ρ (ℓ : Module.Dual ℂ S) v
              (fun j => CartanQuotient.representative T (lam j))‖ ≤
            c * ∏ j, CartanQuotient.delta T (lam j) ^ ((1 : ℝ) / 2 - η)

end Langlands
