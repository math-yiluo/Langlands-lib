# A common special compact for packet estimates

`HasSpecialPacketCompact` asks for one compact open subgroup of the actual
rational points at the prescribed maximal split torus and generic
cocharacter. It must satisfy `WeakExpansion.IsSpecialVertexCompact` with
the apartment axioms and bounded open stabilizers, the full ambient
parabolic product family, the simultaneous standard basis, and the ambient
and standard-Levi Cartan covers. Every property uses the same subgroup.

`hasSpecialPacketCompact_of_availability` derives this package from the
published `BruhatTitsAvailabilityStatement`. The proof rebases a valid
assignment to the prescribed torus and chooses one special vertex. It
uses the apartment axioms and bounded stabilizers of the rebased assignment
and applies the published `availableSimultaneousStandardBasis` and
`Iwasawa.availableIwasawa` at that vertex. The published
`validSpecialCompactRenardCartanComparison` supplies the compatible ambient
and Levi data used by `rationalPositiveCartanCover` and
`standardLeviCartanCovering_of_compatibility`. Equality of the based torus
and embedding carries these witnesses to the original parameters.

This is a derived structural input to the weak-term argument in Waldspurger
VI.3.1. It retains at the same special compact the validated apartment
required by the Library's weighted weak expansion. The proof depends on
global Bruhat–Tits availability.
