# Original curve-place fixed-model Weil comparison on full adeles

This is the function-field fixed-integral-model assembly in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pp.9–10. The construction keeps the original integral bases,
compares their actual points at enlarged supports and full upper
preimages, and passes to the actual full adele rings. Its intermediate
colimit and continuity lemmas are derived implementation tools for this
passage.

All fields share an arbitrary universe. Let k be a finite field, K a
function field over k with its specified rational-function presentation,
and L a finite extension of K with compatible k-algebra structures.
There is no separability hypothesis on L/K. Choose s in K for which
K/k(s) is finite, and a nonzero t in the integral chart ring
`CurveModel.chartRing k {s}`. Write S for
`curvePlacePrincipalExceptional k K s (t : K)`, S' for its full upper
preimage, A for `curvePlaceSIntegers k K S`, and B for
`curvePlaceSIntegers k L S'`. Thus this unit retains the principal-chart
initial supports of the underlying finite-projective integral
construction; it does not assert a new integral finiteness theorem for
every initial support.

Let Y be a scheme over Spec B, locally of finite type and
quasi-compact, with a specified relative immersion j into P^n_B. The
equation identifying j followed by the projective-space structure map
with Y's structure map is explicit. Relative separatedness follows from
this immersion, and quasi-separatedness of Y follows over the affine
base. Neither is an extra premise. The published principal-chart
construction supplies the finite-projective B/A structure.

`pointCoconeIsColimit` is a more general lemma: for arbitrary fields k
and F with a k-algebra structure, any finite set S of actual curve
places, and an actual model X over the corresponding S-integer ring,
local finite presentation of X suffices. Its cocone point consists of
actual morphisms to X over that original base from the spectrum of the
full curve-place adele ring. Its legs are coefficient changes along the
literal level inclusions. The proved
`curvePlaceFixedModelPointComparisonProperties` supplies bijectivity of
the canonical point-colimit map, which Mathlib's Type-colimit criterion
turns into an `IsColimit` witness for this cocone. This lemma requires
neither separation nor quasi-compactness.

`upperTransition_continuous` proves continuity of the original upper
point transitions at arbitrary enlarged upper supports. The proof
constructs the rational-function algebra action on L by composing the
given action on K with K → L, proves the two scalar-tower laws, and
deduces `FunctionField k L` by transitivity of finite modules. It then
applies the existing fixed-model transition-topology theorem. Thus no
extra choice of an upper function-field presentation is a premise.
This helper does not require the finiteness of K/k(s) or nonvanishing
of t; those hypotheses are used by the integral Weil construction.

`stageNatIso` compares the original lower point diagram of
`affineChartWeilRestriction A B Y` with the original upper point diagram
reindexed by `curveUpperLevelFunctor k K L s t`. The component at each
lower support is the actual `adelicLevelPointHomeomorph`. Its naturality
is `CurvePlaceFixedLevelWeilEvaluation.levelPoint_natural` for the
literal support inclusions. Throughout this diagram, A and B remain
the original bases.

`adelicPointHomeomorph` constructs a homeomorphism

    (Res_(B/A) Y)(CurvePlaceAdeleRing k K) ≃ₜ Y(CurvePlaceAdeleRing k L).

Both sets are the actual fixed-model scheme points from
`CurvePlaceFixedModelAdelePoints`. Their topologies are the respective
`curvePlaceFixedModelAdelePointTopology`, each independently defined as
the final topology from its original stage spaces. The comparison does
not define either topology by transport.

The proof applies `finalCoconeHomeomorph` to the actual point cocones,
the two colimit witnesses, and `stageNatIso`. Full-preimage support
cofinality gives the required final functor. The upper transition
continuity comes from the helper above, and the component homeomorphisms
are the original level homeomorphisms. The lower S-integer ring is
noetherian by the published principal-chart result. Finiteness of B
over A gives noetherianity of B using
`IsNoetherianRing.of_finite`. Local finite presentation of Y follows
from local finite type over that noetherian base. The lower Weil model
is locally of finite type by the published
`AffineChartWeilRestrictionFiniteType` instance, hence locally of
finite presentation by the same implication. No assumed colimit,
comparison, transition-continuity or finite-presentation package
replaces these proofs.

`adelicPointHomeomorph_stage` states that including any original lower
stage point in full adeles and then applying the full homeomorphism
equals applying its original level homeomorphism and then the literal
upper stage inclusion. The separatedness and quasi-separatedness
instances in the proposition are derived from j. Unfolding the
constructed homeomorphism and applying `finalCoconeHomeomorph_ι`
proves exactly this stage law.

This unit concerns the original fixed integral models on full curve
adeles. The comparison of their generic fibers with the original
field-level Weil restriction, and of their fixed-model final topologies
with the spread topologies on generic fibers, remain separate host
obligations. No completion of Example 4.2 or of the whole paper is
claimed.
