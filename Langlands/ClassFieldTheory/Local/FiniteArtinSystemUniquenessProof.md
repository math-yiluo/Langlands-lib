# Uniqueness of coherent geometric finite Artin systems

Author: Worker 1771.

The theorem `Langlands.LocalClassField.geometricFiniteArtinSystemUniqueness`
proves the published proposition
`Langlands.LocalClassField.GeometricFiniteArtinSystemUniqueness.{u}`.
It retains every prime `p`, every `PadicField.{u} p`, every supplied
`F.TopologicalData`, and both actual finite families satisfying the entire
`GeometricFiniteArtinSystemRelation`. No hypothesis is added to that
proposition. This unit proves uniqueness; the coherent existence required
by `GeometricFiniteArtinSystemExistenceUniqueness` remains a separate
obligation.

## Supplied residue normalization

The helpers in `FiniteArtinSystemUniqueness` compare the given normalization
with the existing arithmetic coordinates on actual unramified extensions.
`residueCardinality_eq_canonical` identifies the supplied and canonical
integer subrings through their common characterization by the canonical
norm. Their residue fields are then equivalent, so their cardinalities
agree. `discreteValuation_le_one` observes that membership in the supplied
integer ring implies the required discrete valuation bound, using the
order isomorphism defining that discrete valuation.

For independently quantified carrier universes of the base and extension,
`residueHom_inverse_power` turns the inverse-automorphism congruence into
an equality on the actual relative spectral residue field. It lifts a
residue class to an integer, uses
`ArithmeticCoordinate.extensionIntegerEquiv` and
`ArithmeticCoordinate.extensionResidueEquiv`, and applies
`NYLL.suppliedResidueCongruence`. The exponent and inverse convention are
preserved. `inverse_coordinate_eq_one` applies injectivity of the residue
action in an arithmetic unramified coordinate. The inverse automorphism
has the same residue action as arithmetic Frobenius; consequently its
arithmetic coordinate is `Multiplicative.ofAdd 1`.

## Cyclic probes and separation

For each positive integer `N`, `cyclic_probe` uses
`unramifiedExtensionDegreeExistence` to choose an actual unramified
Galois intermediate extension of degree `N`, and
`ArithmeticCoordinate.coordinate_exists` to obtain its arithmetic cyclic
coordinate. This coordinate shows that the extension is abelian.
Its inverse coordinate, composed with the actual `abelianRestriction`,
gives a continuous homomorphism from the absolute Galois abelianization to
`Multiplicative (ZMod N)`. The supplied geometric congruence, specialized
to the canonical topological data of this extension, makes every
normalized profinite homomorphism send every base element of order one
to the same positive generator under this probe. This construction needs
no finite Artin family as an existence input.

`profinite_eq_of_ord_eq_one` compares two profinite homomorphisms satisfying
the geometric relation. Their exact finite norm kernels give equal
membership in every open subgroup of the absolute Galois abelianization,
by `WeilReciprocityUniqueness.mem_openSubgroup_iff`. Together with the
cyclic probes, the compact Hausdorff nonarchimedean separation theorem
`ReciprocitySystemUniqueness.eq_of_forall_openSubgroup`, at the nonzero
integer `d = 1`, identifies their values on each element of order one.
Compactness and the Hausdorff and nonarchimedean quotient structures come
from the actual absolute Galois group and its topological abelianization.

`profinite_eq` extends this equality to every element of `F.Carrierˣ`.
Choose the existing uniformizer unit `π`, and for an arbitrary `x` set
`k = 1 - T.ord x`. The element `x * π ^ k` has order one. Equality there
and at `π`, multiplicativity and the integer-power law give equality at
`x` by cancellation. Extensionality then identifies the continuous
homomorphisms.

## Recovery of the entire finite family

The closing theorem reconstructs a profinite homomorphism from each of
the two coherent finite families using
`FiniteArtinReconstruction.reconstruct`.
`ProfiniteReciprocityReconstruction.reconstruct_geometric` supplies its
geometric relation from precisely the hypotheses of the uniqueness
statement. Apply `profinite_eq`, then recover both actual finite families
with `FiniteArtinReconstruction.finiteFamilyOfHom_reconstruct`. This
proves equality of the entire dependent families, including all their
actual finite abelian extension indices.

## Provenance and scope

These are internal derived results from the published definitions,
residue comparisons, unramified extension theorems and conditional
reconstruction results. The implemented proof follows the route above;
it makes no separate claim to reproduce a proof in the original
literature. Reconstruction is applied only to the two given coherent
families. No downstream profinite existence theorem, arithmetic Artin
map, coherent-family certificate or desired bijectivity is assumed.
The original full existence-and-uniqueness target and its imports are
preserved.
