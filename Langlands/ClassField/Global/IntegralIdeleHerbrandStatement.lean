import Langlands.ClassField.Global.IntegralIdeleCoefficients
import Langlands.ClassField.Global.IdeleArchimedean
import Langlands.ClassField.Global.ArchimedeanHerbrandFactor
import Langlands.Cohomology.HerbrandQuotient

/-! # The Herbrand quotient of the integral ideles (statements)

Statements only: for a cyclic Galois extension of number fields, the integral ideles `J∞` have
Herbrand quotient `D∞`, the product over the orbits of infinite places of the stabilizer orders;
and the archimedean local input, the Herbrand quotient of `E_wˣ` under the stabilizer of an
infinite place `w`.
-/

namespace Langlands.ClassField.Global

open NumberField
open Langlands.Cohomology.Herbrand

universe u v

/-- `h(J∞) = D∞`: for a cyclic Galois extension `E / F` of number fields in independent
universes, the first and second cohomology groups of the integral ideles are finite and
`|H²(Gal(E/F), J∞)| = D∞ · |H¹(Gal(E/F), J∞)|`, where `D∞ = archimedeanHerbrandFactor F E`. -/
def CyclicIntegralIdeleHerbrand : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (E : Type v) [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)],
    Finite (integralIdeleCohomology F E 1 : Type v) ∧
      Finite (integralIdeleCohomology F E 2 : Type v) ∧
      Nat.card (integralIdeleCohomology F E 2 : Type v) =
        archimedeanHerbrandFactor F E * Nat.card (integralIdeleCohomology F E 1 : Type v)

/-- The archimedean local input: for a Galois extension `E / F` of number fields and an infinite
place `w` of `E`, the units `E_wˣ` of the completion, under the stabilizer `D_w` of `w`, have
finite first and second cohomology with `|H²(D_w, E_wˣ)| = |D_w| · |H¹(D_w, E_wˣ)|`. -/
def ArchimedeanCompletionHerbrand : Prop :=
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (w : InfinitePlace E),
    HasHerbrandQuotient (infiniteLocalRepresentation F w)
      (Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w))

end Langlands.ClassField.Global
