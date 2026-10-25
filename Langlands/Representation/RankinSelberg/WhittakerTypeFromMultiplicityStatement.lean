import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Whittaker type from a nonzero spanning functional

This proposition is an internal algebraic adapter. Existence of a nonzero
functional and the scalar-multiple property remain explicit hypotheses.
-/

namespace Langlands.RankinSelberg

open GeneralLinear

universe uF uV

/-- An irreducible admissible representation with a nonzero functional spanning
the full character-equivariant functional space is of Whittaker type. -/
def WhittakerTypeFromMultiplicityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F],
    ∀ (n : ℕ) (θ : upperUnipotent (n + 1) F →* ℂˣ),
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V,
      Representation.IsIrreducible π → IsAdmissible π →
      (∃ ℓ : Whittaker.functionals (upperUnipotent (n + 1) F) θ π,
        ℓ.val ≠ 0 ∧
        ∀ ℓ' : Whittaker.functionals (upperUnipotent (n + 1) F) θ π,
          ∃ c : ℂ, ℓ' = c • ℓ) →
      IsOfWhittakerType n θ π

end Langlands.RankinSelberg
