# Original number-field fixed-model Weil comparison on full adeles

This is the number-field fixed-integral-model assembly in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pp.9–10. Conrad keeps one pair of integral models over the
initial rings, compares their points at every enlarged support and its
full upper preimage, and passes to the direct limit. This derived unit
performs that passage on the actual full adele rings. It uses the actual
level homeomorphisms and their proved support naturality.

All fields share an arbitrary universe. Let K and L be number fields
with their specified K-algebra structure on L, let S be a finite set of
finite places of K, and write S' for its full upper preimage. All
infinite places are included in every level. Put A = O(K,S) and
B = O(L,S'). Let Y be an actual scheme over Spec B, locally of finite
type and quasi-compact, equipped with a relative immersion
j : Y → P^n_B. The equality identifying its composite with the
projective-space structure map with Y's structure map is explicit.
No additional separatedness or quasi-separatedness assumption is
imposed: the immersion supplies relative separatedness, which supplies
quasi-separatedness over the affine base. Number-field finiteness gives
the existing finite-projective B/A structure.

`pointCoconeIsColimit` applies to an arbitrary actual model X over
Spec A that is locally of finite presentation, without requiring
quasi-compactness or separation. Its cocone point is X evaluated at the
actual full adele ring, with its original A-algebra action. The stage
maps are spectra of the literal inclusions of the adelic levels.
The previously proved `numberFieldFixedModelPointComparisonProperties`
gives bijectivity of the canonical point-colimit map. Mathlib's
Type-colimit criterion turns that bijectivity into an `IsColimit`
witness for this very cocone.

`stageNatIso` compares the actual lower point diagram for the
`affineChartWeilRestriction A B Y` with the actual upper point diagram
reindexed by `numberFieldUpperLevelFunctor K L S`. Its components are
the original `adelicLevelPointHomeomorph`, without replacing their maps
by arbitrary equivalences. The naturality square is exactly
`NumberFieldFixedLevelWeilEvaluation.levelPoint_natural` for the
literal lower and upper support inclusions, over the unchanged A and B.

`adelicPointHomeomorph` is a homeomorphism

    (Res_(B/A) Y)(Adeles K) ≃ₜ Y(Adeles L).

Here both sets consist of the actual morphisms over the fixed integral
bases, as in `NumberFieldFixedModelAdelePoints`. Each topology is its
existing `numberFieldFixedModelAdelePointTopology`, defined independently
as the final topology from its own original stages. Neither topology is
transported across the comparison.

The construction applies `finalCoconeHomeomorph` with the actual point
cocones and `stageNatIso`. The upper-support functor is final by the
proved full-preimage cofinality result. Upper transitions are continuous
by `numberFieldFixedModelTransitionTopology`; the components are the
original stage homeomorphisms. The two Type-colimit witnesses come from
`pointCoconeIsColimit`. Local finite presentation of Y follows from
local finite type over its noetherian S-integer base. For the lower
Weil model it follows from the existing
`AffineChartWeilRestrictionFiniteType` instance and the same
noetherian-base implication. Thus no colimit comparison, continuity
assertion or presentation hypothesis needed for this application is
left as an assumed package.

`adelicPointHomeomorph_stage` identifies the constructed map on every
lower stage: including a lower point in full adeles and then applying
the homeomorphism equals applying its original level homeomorphism and
then the literal upper level inclusion. Its proposition introduces only
the separatedness and quasi-separatedness instances derived from j,
so these do not become extra hypotheses. The proof specializes the
stage law of `finalCoconeHomeomorph`.

This unit concerns the original fixed models on full adeles. Identifying
their generic fibers with the original field-level Weil restriction,
and comparing the fixed-model final topology with the spread topology
on those generic fibers, remain separate host obligations. The
function-field case is also separate; no whole-paper completion is
claimed here.
