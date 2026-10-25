# Pullback of geometric-equivariant coefficient inverse systems

This internal construction proves that the complete coefficient inverse system
from `EtaleEquivariantAdicSystem` commutes with the actual equivariant etale
pullback functor. It also identifies the canonical cone maps under that
comparison. Its provenance is the existing scalar-extension and restriction
pullback isomorphisms and the epimorphic quotient units; it does not transcribe
an external theorem or assume the desired compatibility.

## Parameters and geometric convention

The schemes `X` and `Y`, commutative coefficient ring `R`, and module carriers
share universe `u`. The group `G : Type w` has independent universe `w`. The
ideal `I : Ideal R` is arbitrary. All powers indexed by natural numbers occur,
including zero. The group actions are homomorphisms to opposite automorphism
groups, as in `EtaleCohomologyAction`. The map `f : Y ⟶ X` is etale and is
supplied with its equivariance equation

`f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f`.

The pullback is the existing restriction functor on actual small-etale module
sheaves with its constructed geometric equivariance. No topology on `G` is
required or supplied.

## Level comparison and units

Write `P` for equivariant pullback and `Q_X(n)` for the existing scalar
extension along `R → R/I^n` followed by restriction of scalars on `X`.
`equivariantPowerPullbackIso` constructs

`Q_X(n) ⋙ P ≅ P ⋙ Q_Y(n)`.

It first moves scalar restriction through geometric pullback using
`scalarRestrictionEquivariantPullbackIso`, then moves scalar extension using
`scalarExtensionEquivariantPullbackIso`. Functor associators align the
parentheses. Thus the comparison uses the actual existing coefficient
functors and their constructed maps.

`equivariantPowerPullbackIso_unit` states that the pullback of the extension
unit, followed by this comparison, is the extension unit after pullback. Its
proof reduces the composite formula to the previously proved
`scalarExtensionUnit_equivariantPullback`.

## Transition compatibility and the whole inverse system

`equivariantPullback_unit_epi` proves that the pulled-back coefficient unit is
an epimorphism in the equivariant category. The underlying unit is epimorphic
by `extensionUnit_app_epi`. Ordinary etale restriction is a left adjoint by
`restrictionAdjunction`, so it preserves that epimorphism. The faithful
forgetful functor from equivariant sheaves reflects epimorphisms.

`equivariantPowerPullbackIso_transition` proves that the level comparisons
commute with every transition from a higher power `n` to a lower power `m`.
The proof precomposes the desired square with the just-proved epimorphic unit.
Functoriality, the transition-unit equations, and the level comparison's unit
equation identify the resulting composites. Cancellation then proves the
square without a new transition or compatibility hypothesis.

`equivariantFunctorPullbackIso` assembles the level comparisons into a natural
isomorphism of functors to the category of `ℕᵒᵖ` diagrams. Its inner naturality
is the transition equation; its outer naturality is that of the level
comparisons in the input equivariant sheaf. Finally,
`equivariantFunctorPullbackIso_unit` identifies each pulled-back leg of
`equivariantQuotientCone` with the canonical leg on the pulled-back sheaf.

These are ordinary inverse systems and cone maps. The file does not assert
that the cone is limiting, that coefficient reduction is exact, or that
pullback commutes with a completion, derived inverse limit, or cohomology.
It supplies no smoothness or continuity assertion. Actual Harris level
schemes, finite etale level-cover torsors, and their descended associated
coefficient sheaves remain separate dependencies. In particular, no
commutation of tensor reduction with taking group invariants is assumed here.
