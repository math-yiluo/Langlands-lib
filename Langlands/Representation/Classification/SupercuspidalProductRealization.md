# Small supercuspidal factors in actual normalized products

Author: Worker 1768.

This internal construction realizes actual supercuspidal representations on
carriers in any independently prescribed universe. It preserves
unitarizability and gives an equivalence of the entire normalized product
induction. The field, original block, replacement block and source-action
carrier universes are independent.

`exists_supercuspidal_realization` applies the proved
`padicIrreducibleSmoothSmallRealization` to the underlying irreducible smooth
representation. The resulting equivalent smooth representation remains
supercuspidal by `GeneralLinear.isSupercuspidal_of_equiv`: admissibility and
vanishing of the actual conjugate-parabolic Jacquet quotients transport along
the equivalence. `supercuspidalRealization` chooses such a model, and
`supercuspidalRealizationEquiv` supplies its actual representation equivalence.
The construction uses exactly the supplied `T.topology`.

`isUnitarizable_supercuspidalRealization` transports the existing invariant
positive form through that equivalence, using
`isUnitarizable_iff_of_equiv`. No unitarity or irreducibility conclusion about
an arbitrary induced representation is used.

`supercuspidalProductRealizationEquiv` applies the published
`normalizedProductInducedEquiv` to the family of block equivalences. This
retains the same ordered block shape, the same actual general linear group,
the standard upper block parabolic and its original half-modulus
normalization. It compares the entire induced representations.

`exists_unitary_supercuspidal_product_equiv` starts with a supplied
equivalence from an original representation `ρ` to such a product, whose
supercuspidal factors are unitarizable. Composition with the preceding
equivalence provides factors in the prescribed replacement universe, their
unitarizability, and an equivalence from the same original action `ρ` to the
entire replacement product. In particular, replacement block carriers may
lie in the field universe even when the original blocks and `ρ` have other
carrier universes.

The provenance is internal and derived from the proved small-realization
theorem and the published supercuspidality, positive-form and induction
transport constructions. It adds no original-source assertion about
universes. For the associated-pair induction task, this removes a carrier
universe mismatch after unitary supercuspidal blocks and the original
equivalence have been established. Their existence, the classification,
factor comparisons and the main associated-pair theorem remain separate
proof obligations.
