# The top line of an unramified inducing product

This internal helper for the ordered unramified Whittaker realization identifies
the whole top derivative of the normalized singleton-block inducing product
with the complex line. It then proves that the standard-character coinvariant
space of that product has complex dimension one.

The proof starts with the rank-one character quotient. Its upper-unipotent
group is trivial, as follows by its identification with the upper subgroup of
the trivial rank-one mirabolic group. Every localization relation is therefore
zero. `Submodule.quotEquivOfEqBot` identifies the quotient with the original
lifted complex line, and `ULift.moduleEquiv` removes that lift. This argument
works for every character of the rank-one upper group.

`coinvariantsTopDerivativeEquiv` takes the component of the all-field
`TopLocalization.topLocalizationIso`, which compares the whole upper-character
quotient with the top derivative. The derivative's terminal rank is transported
from `m - m` to zero. The private `rankCastCarrierEquiv` removes this transport
on the coefficient space by eliminating the rank equality. Composing the
inverse of this comparison with the rank-one quotient equivalence gives
`rankOneTopDerivativeLineEquiv`.

`productTopDerivativeLineEquiv` applies the all-field
`finiteProductTopDerivativeLineEquiv` to the shape of `n + 1` singleton blocks.
Each block has rank one and its top derivative is the line just constructed.
The result is a linear equivalence from the entire product's top derivative
to the complex scalars. For `finrank_productCoinvariants`, rewrite the
entrywise character as the standard character, apply invariance of finite
dimension to both equivalences, and compose the resulting dimension equalities.

The derivative and induction imports are published Library modules in the
`Langlands.AllFieldBZ` namespace. They use `LocalFieldPackage` and
`LocalFieldData` and apply over every nonarchimedean local field, including
positive characteristic.

These are derived consequences of the imported derivative and localization
comparisons, specialized to the concrete rank-one unramified character blocks
defined in `OrderedUnramifiedRankOneBlocks`. The product calculation implements
the top-degree case of the Bernstein–Zelevinsky derivative product rule
(Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*,
1977, §4); the paired Markdown of the imported modules records their precise
source correspondence. The elementary rank-one calculation is an internal
derivation from the matrix definitions and quotient construction.

The final theorem concerns the actual normalized inducing product, before
transport to the concrete principal-series model. It assumes an arbitrary
nonarchimedean local field, a uniformizing element, nonzero unramified
parameters, and a `UnitaryAdditiveCharacter`. It needs no order condition on
the parameter norms, no irreducibility, no residue-cardinality choice, and no
additional conductor or nontriviality hypothesis on the character.
