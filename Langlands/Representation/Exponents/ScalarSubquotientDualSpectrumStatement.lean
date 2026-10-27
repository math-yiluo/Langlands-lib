import Langlands.Representation.Exponents.DualJacquet

/-!
# Scalar subquotients detected by generalized full-dual spanning

This internal algebraic proposition states that an actual nonzero scalar
subquotient has a character among any family whose generalized spaces span the
full algebraic dual. It imposes no dimension hypothesis and contains no proof.
-/

namespace Langlands

universe uK uA uV uW

/-- Generalized character spanning on the full transpose dual detects the
scalar character of every actual nonzero subquotient. -/
def ScalarSubquotientDualSpectrumStatement : Prop :=
  ∀ (K : Type uK) [Field K] (A : Type uA) [CommGroup A]
    (V : Type uV) [AddCommGroup V] [Module K V]
    (ρ : Representation K A V) (P : (A →* Kˣ) → Prop),
    (⨆ (χ : A →* Kˣ) (_ : P χ),
      (generalizedCommutativeCharacterSpace (commutativeTranspose ρ) χ).toSubmodule) = ⊤ →
    ∀ (χ : A →* Kˣ) (U : Subrepresentation ρ)
      (W : Type uW) [AddCommGroup W] [Module K W] [Nontrivial W]
      (q : U.toSubmodule →ₗ[K] W),
      Function.Surjective q →
      (∀ (a : A) (u : U.toSubmodule),
        q (U.toRepresentation a u) = (χ a : K) • q u) →
      P χ

end Langlands
