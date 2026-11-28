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

## Construction from the root-valuation building

`specialPacketCompact` chooses an open subgroup with every clause of
`HasSpecialPacketCompact`. The theorem `hasSpecialPacketCompact` gives the
existential form. Both apply to any connected reductive group over a
nonarchimedean local field, at the displayed maximal split torus and generic
cocharacter.

The construction starts from `valuationApartmentAxiomsExistence`. Maximal
split torus conjugacy and `ValuationBuildingData.basedTransport` put the
apartment at the prescribed torus. The parahoric extension
`ParahoricBuildingData.exists_toValuationBuildingData_eq` keeps that
apartment. `ParahoricBuildingData.fiveAxioms_of_statements` uses
`actualApartmentSplitting`, `affineIwahoriTits` and `affineIwahoriTitsBuilding`
to give the geometry for `metricRealization`. `rootGroupActionAxiom` gives
the zero-fixer generators. The local building versions of compact
maximality and Iwasawa, together with
`parahoricCartanConclusions_of_buildingGeometry`, supply the ambient
comparisons. The compact is the norm-one stabilizer of a special vertex.

For each standard Levi, the construction uses the same local geometry at
the factor of the ambient maximal split torus. The restriction of the
ambient vertex gives a special vertex in the resulting Levi apartment.
`exists_specialCompactLevi_of_buildingGeometry` identifies its compact
with the literal preimage of the ambient compact. The Cartan comparison
transports across this equality using
`specialCompactCartanComparison_on_subgroup_of_heq`. The Levi maximality
gives `hasParabolicFactorization_of_maximal_compact_levis` in the ambient
group. The two Cartan covering lemmas turn the comparisons into the
published ambient and standard-Levi covers.

At the ambient vertex, `centralizerFiltrationDoubleRootExistence`
provides the open double-root-friendly filtration. The
`simultaneousStandardBasisAt_of_doubleRootFiltration` theorem uses the
original positive-depth Moy–Prasad subgroups to give the simultaneous
basis for that same compact. This route uses local building and
filtration results independently of the integral-model axioms.

The geometric steps use Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), §§5.2–5.3 and §§9.5–9.8, with the authors' corrections.
Their use in the wave-packet argument follows Waldspurger (2003),
I.1 and VI.3.1, printed pp. 240–241 and 302–305.

`semistandardLeviCompactTrace` realizes the special compact on an actual
semistandard Levi as the inverse image of the given ambient compact. It
chooses a chamber in which the outer parabolic is standard and uses its
standard Levi scheme as the actual model. In the apartment of this Levi,
the restriction of the ambient special vertex is special. The comparison
of the two compact stabilizers identifies the Levi stabilizer with the
literal ambient trace. The Levi compact inherits all special compact
properties and the minimal Iwasawa factorization at the original generic
cocharacter, through the literal factor of the ambient split torus.
This realizes the compatibility of the compact with the Levi in
Waldspurger I.1, printed p. 240, used in the nested diagram of III.6
and VIII.2.1.
