import Langlands.Representation.Classification.Essential

/-!
# Scalar norms from arbitrary unitary exponent data

An internal derived proposition: if an element acts by a scalar on a nonzero
carrier, then every unitary exponent witness determines the norm of that
scalar as the corresponding real power of the positive character. This is a
proposition definition, not a proof.
-/

open scoped NNReal

namespace Langlands

/-- For every unitary exponent witness `u` of an actual representation `ρ` on a
nontrivial carrier, an element `g` acting by the scalar `c` satisfies
`‖c‖ = ν(g) ^ u.exponent`. -/
def UnitaryExponentScalarNorm.{uG, uV} : Prop :=
  ∀ (G : Type uG) [Group G] (V : Type uV) [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ν : G →* ℝ≥0ˣ) (ρ : Representation ℂ G V)
    (u : UnitaryExponentData ν ρ) (g : G) (c : ℂ),
    (∀ v : V, ρ g v = c • v) →
      ‖c‖ = (((ν g : ℝ≥0) : ℝ) ^ u.exponent)

end Langlands
