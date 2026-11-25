# Geometry of representatives constructed from normalized families

This auxiliary module supplies geometry for the representation-free construction
`GroupIsomorphismScheme.ofNormalizedFamily`. It retains that construction's
assumption of a natural family `e` over a label scheme `Q` and a unique
inverse-twist decomposition on every relative scheme test.

The representative has parameter `A.X ⊗ Q`. Its structure morphism is smooth
when both factors are smooth and separated when both factors are separated.
Each proof writes the structure morphism as a base-changed projection followed
by the structure morphism of `A`, then uses stability under base change and
composition.

For flat quasi-compact `A`, `outerOfNormalizedFamily` has parameter `Q`, so it
inherits separatedness and étaleness from `Q`. Its class map equals the second
product projection. The class map is therefore affine when `A` is affine and
smooth when `A` is smooth, by base change.

`ofNormalizedConstantFamily_geometry` specializes these results to the
published `constantParameter S D`, for any type `D : Type u`. With a smooth
affine acting group it gives a smooth separated isomorphism representative,
a separated étale outer parameter, and an affine class map. There is no
finiteness assumption on `D` and no restriction on the base scheme.

`ofNormalizedConstantFamilyWithGeometry` retains this data as a dependent pair:
the constructed full representative, its constructed outer quotient, and proofs
of the five geometry properties above. It uses exactly the product representative
and quotient already described; it makes no additional choice or existence
assumption.

The provenance is the product construction and the existing stability
theorems for scheme morphisms, together with the published separated étale
geometry of `constantParameter`. The input classification data are assumed;
this module does not prove their existence or perform descent.
