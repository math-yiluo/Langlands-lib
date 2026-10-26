# Reduction of associated coefficient sheaves

Author: Worker 13.

Let `R : Type u` be a commutative ring, `I : Ideal R`, `G : Type u` a group,
`X : Scheme.{u}`, and `Y : Action X.Etale G`. Module carriers share universe
`u`. All sheaves use the actual small etale site of `X`. The geometric action
`Y` is arbitrary; no covering or torsor property is required for these
invariant-sheaf constructions.

This is an internal construction from the actual quotient functors in
`Langlands.Coefficients.AdicSystem`, their tensor presentations in
`AdicTensorComparison`, the sheaf tensor presentation in
`Langlands.Geometry.EtaleAdicTensorComparison`, and the constant associated
comparisons in `ConstantScalarCompatibility`, `ConstantScalarExtension`
and `ConstantScalarRestriction`. The associated functor is the existing
invariant-limit construction in `Associated`. No result from Harris is
independently transcribed here.

`moduleTensorReductionActionIso` and `moduleTensorPowerActionIso` transport the
existing natural module tensor/quotient identifications to full group actions.
`modulePowerReductionUnit` and `modulePowerReductionTransition` carry the actual
quotient maps and power transitions, with equivariance and naturality proved from
the corresponding module natural transformations. Their identity, composition
and unit-transition laws assemble `modulePowerReductions`, a functor from
`ℕᵒᵖ` to endofunctors of `Action (ModuleCat R) G`. All these proofs forget
to underlying modules and use the existing natural quotient maps and their
laws. `moduleTensorPowerActionIso_unit` similarly lifts the existing
tensor-power unit equation: the equivariant tensor unit followed by the
tensor-power comparison is the equivariant quotient map. Index zero is
included, with `I^0 = R`.

`constantAssociatedReductionComparison` starts from the sheaf quotient functor,
passes through its tensor presentation and the canonical associated extension
comparison, and then applies the associated functor to the module tensor/quotient
isomorphism. It is a natural morphism to the associated quotient-ring coefficients.

`constantAssociatedPowerReductionComparison` retains the initial scalar ring. It
uses the inverse sheaf extension-power isomorphism, restricts the canonical
associated extension comparison, applies the constant associated restriction
isomorphism, and finally uses the equivariant module tensor-power isomorphism.
Writing `A` for `constantAssociatedFunctor X.smallEtaleTopology Y`, `Qₙ`
for the sheaf power-reduction endofunctor, and `Pₙ` for the equivariant module
power-reduction endofunctor, its direction is

`Cₙ : A ⋙ Qₙ ⟶ Pₙ ⋙ A`.

`constantAssociatedPowerReductionComparison_unit` proves at every coefficient
action `M` that

`qₙ(A M) ≫ Cₙ(M) = A.map ((modulePowerReductionUnit I n).app M)`,

where `qₙ` is the actual sheaf quotient map. The proof writes `qₙ` as the
sheaf tensor unit followed by the sheaf tensor-power comparison and cancels
that comparison against its inverse in `Cₙ`. The existing
`constantAssociatedScalarChange_unit` identifies the next three factors
with the associated image of the equivariant tensor unit. Functoriality
and `moduleTensorPowerActionIso_unit` give the displayed equation.

For `h : m ≤ n`, write `sₙₘ : Qₙ ⟶ Qₘ` for the existing sheaf transition
and `tₙₘ : Pₙ ⟶ Pₘ` for `modulePowerReductionTransition I h`. The theorem
`constantAssociatedPowerReductionComparison_transition` proves

`(A ◁ sₙₘ) ≫ Cₘ = Cₙ ≫ (tₙₘ ▷ A)`.

The symbols denote left and right whiskering. At each coefficient action,
the proof cancels the existing epimorphism `qₙ(A M)` from
`Langlands.Sheaf.AdicSystem.quotientMap_app_epi`. The sheaf quotient-unit
transition law, the new unit equation at both indices, and the equivariant
module unit-transition law then identify the two composites. There is no
sectionwise-surjectivity assumption and no assumed comparison square.

`constantAssociatedModuleReductionFunctor` sends `M` to the inverse system
`n ↦ A(Pₙ M)` with the constructed transitions. It is obtained by flipping
`modulePowerReductions` and postcomposing with `A`.
`constantAssociatedReductionSystemsComparison` is a natural transformation
from `A ⋙ EtaleAdicSystem.functor X I` to this functor. Its component at
`M` and `n` is exactly `Cₙ(M)`. Transition coherence proves that the
components form an inverse-system morphism; naturality of each `Cₙ`
proves naturality in every equivariant coefficient-module map.

These are ordinary sheaves and ordinary inverse systems. No finiteness,
flatness, torsor, completeness or topology on the coefficient group is
assumed. The construction supplies a comparison morphism; invertibility,
local triviality, smoothness, derived inverse limits, cohomology comparison
and the identification with Harris's specialized geometric coefficient
systems remain separate obligations.
