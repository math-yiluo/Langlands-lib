# Geometric component counts over Noetherian scheme bases

This internal supporting construction extends the exact affine-base component
count to arbitrary scheme bases and proves constructibility of every level
set over a Noetherian base. It combines the existing actual geometric-fibre
component transport, generic constancy and Noetherian topological induction.
It does not prove the arbitrary-ring host assertion.

`schemeGeometricFibreComponentCount X p` is the extended natural cardinality
of the actual connected components of the quotient point space of the
presheaf product of `X` with the canonical geometric point at `p`. The
topology is the published `pointTopology`. The scheme and algebraic space
lie in the same universe; the point space has the universe prescribed by
`Points`. The affine comparison theorem is definitional equality with
`geometricFibreComponentCount B X p` from the host development.

`schemeGeometricFibreComponentCount_baseChange` assumes an etale surjective
scheme atlas whose structural morphism is locally of finite type and
quasi-compact. For an arbitrary morphism of scheme bases and every point
upstairs, it identifies the upstairs count with the downstairs count at its
image. This is `ENat.card_congr` applied to the actual equivalence
`GeometricComponentTransport.baseChangeGeometricFibreEquiv`. No Noetherian
or quasi-separatedness premise is needed for this comparison.

`exists_open_irreducibleClosed_geometricFibreComponentCount` assumes a
Noetherian base, a quasi-separated algebraic space and the same atlas
hypotheses. For each irreducible closed subset `Z` of the base it constructs
an open `V` such that `Z ∩ V` is nonempty and the counts are equal at every
two points of this intersection.

The proof gives `Z` its actual reduced closed subscheme structure through
`Scheme.IdealSheafData.vanishingIdeal`. Its inclusion `g` has range `Z` and
is a closed immersion. This subscheme is Noetherian by local finite type
and quasi-compactness of `g`, and irreducible by the topology of `Z`.
The pulled-back atlas retains local finite type, quasi-compactness,
etaleness and geometric surjectivity; the space retains quasi-separatedness.
`exists_open_geometricComponentsEquiv` supplies pairwise equivalences of
actual geometric fibre components on a nonempty open `W` of this subscheme.
Because `g` is a topological embedding, `g '' W` equals `Z ∩ V` for an open
`V` of the ambient base. Base-change cardinality equality at two chosen
preimages transports the equivalence to equality of counts at their images.
The topology argument follows the existing reduced-closed-subscheme pattern
in `GeometricallyConnectedConstructibilityFromGeneric`, applied here to the
all-component-count function instead of the connectedness truth value.

`isConstructible_schemeGeometricFibreComponentCount` proves constructibility
of the locus with value any `c : ℕ∞`. On the nonempty relatively open
intersection just constructed, choose a point `p`. If its count equals `c`,
the whole intersection belongs to that level set. Otherwise it is disjoint
from the level set. The published
`SchemeFiberGeometry.isConstructible_of_irreducibleClosed_genericConstancy`
then applies Noetherian induction on closed subsets, decomposing reducible
closed subsets into proper closed subsets. No count-one reduction is used.

`isConstructible_geometricFibreComponentCount_noetherian` specializes to
`Spec B` for any Noetherian commutative ring `B`, a quasi-separated space
satisfying `FinitePresentationOverRing B X`, and every natural number `n`.
The finite-presentation hypothesis supplies an etale surjective atlas whose
structure morphism is locally finitely presented and quasi-compact. Local
finite presentation implies local finite type, so the preceding theorem
applies, and the count agrees definitionally with the host count.

The unrestricted `GeometricFibreComponentsConstructibleStatement` still
requires approximation from arbitrary commutative rings by Noetherian
models. The host statement and its import closure are unchanged.
