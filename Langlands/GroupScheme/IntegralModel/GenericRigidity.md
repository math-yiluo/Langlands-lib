# Generic rigidity and compatible isomorphisms of supplied integral models

Let `R` be a domain with fraction field `K`, and let `M` and `N` be supplied
integral models of actual generic group schemes `G` and `H`. All coefficient
types lie in an arbitrary common universe `u`. No smoothness or reductivity
assumption is needed.

`hom_eq_of_generic` proves that two homomorphisms of the actual model groups
are equal if their generic fibres are equal. The source structural morphism
is flat by the integral-model definition. The target is affine over the
base, hence separated. The published `genericFibre_map_injective` therefore
identifies their underlying morphisms in the over-category. Extensionality
for group-object morphisms identifies the homomorphisms themselves.

For a fixed generic morphism `f`, the compatibility equations of two
`IntegralModel.Hom` values identify their generic fibres after composition
with the same supplied target generic isomorphism. Cancelling that
isomorphism and applying rigidity proves `Hom.hom_eq` and the `Subsingleton`
instance for compatible extensions. This is uniqueness conditional on
existence; it does not construct an extension of an arbitrary generic map.

`Iso.ofHoms` constructs an actual compatible integral-model isomorphism
from extensions of a specified generic isomorphism and its inverse.
Their composites have identity generic fibre, by the two compatibility
squares and the generic inverse laws. Rigidity proves that the actual
model composites are identities. The resulting isomorphism has precisely
the supplied extending maps as its forward and inverse morphisms.
If the generic map is the identity and both extensions exist, the published
original-image transport theorem gives equality of the two original
`integralPoints` subgroups.

`Iso.baseChangeCoefficients` constructs the compatible isomorphism after
changing both the integral and generic coefficient rings through the
commuting coefficient square used by `IntegralModel.baseChange`. It maps
the actual model isomorphism with the group-scheme base-change functor.
The published `Hom.baseChangeCoefficients` supplies compatibility with
the base-changed generic identifications. The forward and inverse maps
are exactly the respective pullbacks of the original maps.

These are internal categorical consequences of the published generic-fibre
injectivity, integral-model compatibility, original-image transport and
coefficient-base-change constructions. They supply the uniqueness and
inverse step once model morphisms have been constructed. They do not
establish existence of a comparison with a canonical model, a building
or a special point, and do not prove `BuildingComparisonStatement`.
