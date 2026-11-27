import Langlands.GroupScheme.Reductive.IdentityComponentClopenReduction
import Langlands.GroupScheme.Reductive.FiberwiseAffinenessProof
import Langlands.GroupScheme.Reductive.MonomorphismClosedImmersionProof
import Langlands.GroupScheme.RelativeIdentityComponent.ClopenQuotientProof

/-! # Proof: reductive fibral identity components are open, closed and of étale index

The conditional assembly `identityComponentClopenReduction` applied to the three proved
inputs `reductiveFiberAffineness`, `reductiveMonomorphismClosedImmersion` and
`RelativeIdentityComponent.clopenQuotient`.
-/

universe u

namespace Langlands.GroupScheme

/-- **Reductive fibral identity components** (Conrad, *Reductive group schemes* (2014),
Proposition 3.1.3), in every universe: for a smooth separated quasi-compact group scheme
`G` over an arbitrary scheme `S` and an open subgroup `i : H ⟶ G` representing the relative
identity component, if every residue-field fibre of `H` is connected reductive, then `H` is
reductive, `i` is a closed immersion, and the fppf quotient `G/H` is represented by a
separated, étale and quasi-compact `S`-group scheme. -/
theorem identityComponentClopen : IdentityComponentClopenStatement.{u} :=
  identityComponentClopenReduction
    reductiveFiberAffineness
    reductiveMonomorphismClosedImmersion
    RelativeIdentityComponent.clopenQuotient

end Langlands.GroupScheme
