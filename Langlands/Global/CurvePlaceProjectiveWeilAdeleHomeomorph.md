# Original function-field projective Weil adelic comparison

This derived construction supplies the generic-fiber and spread-topology
assembly for the function-field case of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
It assembles the previously established original integral-model
homeomorphism, actual generic-fiber identifications and proved
independence of spread topology.

Let k be a finite field, K a function field over k with its specified
rational-function presentation, and L/K an arbitrary finite extension
with compatible k-algebra structures. All fields lie in an arbitrary
common universe. There is no separability hypothesis on L/K. The upper
rational-function algebra structure is the composite through K; its
constant-field tower follows from the original tower identities and
its finite-dimensionality follows by transitivity. The local notation
`withUpper%` inserts these derived instances into declaration types and
proofs. No independently supplied upper presentation or upper
function-field hypothesis is required.

Fix s in K such that K/k(s) is finite, arbitrary finite sets S and T
of lower and upper curve places, an actual scheme X, and a specified
immersion j : X → P^n_L. The original L-scheme `originalScheme` has
structure morphism j followed by the projective structure morphism.
Take `M : CurvePlacePrincipalProjectiveModelData k K L s S T X n j`.
This contains actual arithmetic and geometric model data. For its
nonzero principal denominator d, let E be the places where s is
nonintegral or d is not a unit, and E' its full upper preimage. The
data ensure S is contained in E and T in E'. Its upper integral model
Y over B = O(L,E') has the specified generic fiber X and relative
projective immersion.

The published constructor `curvePlacePrincipalProjectiveModel`
supplies M when X is quasi-compact. The constructor
`curvePlaceFunctionFieldProjectiveModel` supplies the parameter
s = image of RatFunc.X and proves K/k(s) finite from the specified
function-field presentation. Thus neither the parameter nor M assumes
any adelic comparison. Principal supports suffice for this assembly;
the final comparison uses all actual curve places and full adele rings.

Put A = O(K,E). The definition `lowerModel` is the actual integral
Weil scheme `affineChartWeilRestriction A B Y`.
`lowerGenericFiberIso` identifies its actual generic fiber with
`affineChartWeilRestriction K L (originalScheme L X n j)` by the
published `curvePlacePrincipalProjectiveModelWeilGenericFiberIso`.
`upperGenericFiberIso` is M's constructed generic-fiber identification
with the original X. Both use the original integer-subring inclusions
into the original fields.

`adelicPointHomeomorph` constructs

    (Res_(L/K) X)(CurvePlaceAdeleRing k K)
      ≃ₜ X(CurvePlaceAdeleRing k L).

Both endpoints are actual relative scheme morphisms from the spectra
of the full adele rings, as in `CurvePlaceAdelePoints`. Each carries
its own `curvePlaceSpreadAdelePointTopology`, obtained from the
independently defined fixed-model final topology and the specified
generic-fiber equivalence. The upper topology is not defined using
this new Weil comparison.

The homeomorphism is the composite of the inverse lower spread
homeomorphism, the original full fixed-model Weil homeomorphism and
the upper spread homeomorphism. Quasi-compactness of Y's underlying
space follows from its quasi-compact structure morphism over the
affine base. Its specified projective immersion gives relative
separatedness and underlying quasi-separatedness.
`adelicPointHomeomorph_model` proves exact agreement with the
fixed-model comparison under the two generic-fiber identifications,
by cancellation of the lower equivalence and its inverse.
`adelicPointHomeomorph_stage` then proves the restriction equation
for every enlarged lower support U and its full upper preimage.
The lower point enters through the literal coefficient inclusion;
the upper point is obtained by the original
`CurvePlacePrincipalSIntegerFixedLevelRegroup.adelicLevelPointHomeomorph`,
the literal upper inclusion, and the upper spread identification.
The proof applies the model equation and the fixed-model stage law.

`adelicPointHomeomorphOfSpreads` allows independently specified
finite-type spreads P and Q of the original lower Weil scheme and
upper X, over any lower and upper finite place sets U and V.
Local finite type and quasi-compactness of their structure morphisms
are the finiteness assumptions; no additional separation hypothesis
on P or Q is imposed. Their generic-fiber isomorphisms specify which
original field schemes they spread. The construction derives
quasi-compactness of the lower Weil model using
`affineChartWeilRestriction_quasiCompact` and M's finite-affine-
neighborhood property. The two proved
`curvePlaceSpreadTopologyIndependence` equalities then transport the
continuity assertions. The entire underlying equivalence remains
unchanged, so `adelicPointHomeomorphOfSpreads_apply` is proved by
reflexivity.

This unit completes the stated generic-fiber and spread-topology
assembly for function fields. Identification with evaluation of the
original field Weil counit along the literal full-adele inclusion
remains a separate host obligation. The stage law records the precise
original arithmetic maps needed for that identification. Other
assertions of Conrad's five-section paper remain separate obligations.
