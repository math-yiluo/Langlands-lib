# The actual commutator endomorphism of a normalized torus

This internal helper uses the existing normalizing automorphism of an actual
commutative group scheme. It needs neither the torus predicate nor a maximality
assumption.

For a homomorphism `i : T.toGrp ⟶ G` over any base scheme and a point `n` in
`normalizerPoints i`, `torusCommutatorEnd i n` is the actual morphism
`normalizingAut i n .hom - identity`. Homomorphisms of commutative group schemes
use additive notation for their pointwise group law. Consequently, on every test
scheme, the image of this endomorphism under `i` is
`n t n⁻¹ t⁻¹`, with `n` restricted to that test scheme. The proof evaluates the
difference of homomorphisms, applies the normalizing identity, and uses
compatibility of the group laws with composition.

For any morphism `ν : Gm S ⟶ T`, the equation
`ν ≫ torusCommutatorEnd i n = 0` is equivalent to the equality
`ν ≫ (normalizingAut i n).hom = ν`. This follows from distributivity of
composition over subtraction.

Over an arbitrary field, if the underlying scheme map of `i` is monic, the
existing `normalizerPoint_mem_dynamicCentralizer_iff` converts this equality to
membership of the original point `n` in the dynamic centralizer of
`groupHom ν ≫ i`. Thus the last equivalence retains the actual group-scheme
cocharacter and its all-test centralizer, rather than merely a condition on
ground-field points of a kernel.

No assertion of surjectivity, existence of a kernel cocharacter, closedness of
that cocharacter, or the Borel normalizer theorem is made here.
