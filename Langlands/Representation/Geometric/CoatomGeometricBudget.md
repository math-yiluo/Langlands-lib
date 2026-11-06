# Counting represented geometric survivors through coatom labels

This internal unit proves `CoatomGeometricBudgetStatement` in
`Langlands.Aubert.General.RepresentedParabolic`.
It applies the intrinsic finite Coxeter count to the original indices of a
supplied family of actual represented intersection data. The field, inducing
carrier, simple-label type and Coxeter group have independent universes.

For target number `a : Fin n`, the actual geometric data are indexed by
`j : Fin (m a)`. Their surviving indices are precisely
`fullSourceIndices (D a)`, defined by `IsIso (D a j).p'`. Suppose:

- the target labels `I a : Finset B` are injective as a function of `a`;
- each representative-label map `w a : Fin (m a) → W` is injective;
- every `I a` has the cardinality of `J = univ.erase b`;
- each surviving index has a minimal label in `W_(I a) w W_J`;
- each surviving label has `intersectionSubset cs (I a) J w = J`.

Then the sum of all surviving-index cardinalities is at most two. These are
supplied coordinate conditions; the statement does not construct a root
realization or assert that arbitrary chosen labels satisfy them.

The implemented proof forms the finite sigma of all actual surviving indices
and maps `(a,j)` to `(I a,w a j)`. The two injectivity hypotheses make this
map injective. The cardinality, minimality and full-intersection hypotheses
put its entire image inside `fullIntersectionPairs cs J`. The finite sigma
cardinality formula counts every original index, including its multiplicity.
The proved `card_fullIntersectionPairs_coatom_le_two` bounds that image.
There is no replacement of the original family by two selected pieces.

`geometric_labels_injective_of_doubleCoset_coordinates` supplies the second
injectivity condition from actual orbit coordinates. For each target let
`c a` be an equivalence from its original `Fin (m a)` to the literal quotient
`P(k) \ G(k) / Q_a(k)`. A supplied map `lift a : W → G(k)` and the equation
`DoubleCoset.mk ... (lift a (w a j)) = c a j` imply that `w a` is injective:
equal labels have equal lifted points, hence equal quotient classes, hence
equal indices by injectivity of `c a`. Injectivity of the lift is unnecessary.
The lifts may depend on the target. This lemma does not construct the
enumeration, lift or coordinate equation.

The two representation-theoretic corollaries retain the actual field and
topology assumptions, the original proper-source Jacquet vanishing condition,
irreducibility of the inducing representation, isomorphisms of all target
Levis with the source Levi, and supplied geometric gluings. They also require
the above target labels, quotient coordinates and survivor conditions, and
nonzero Jacquet detection of **every irreducible subquotient** of the actual
induction at carrier universe `max u v`.
`hasRepresentedJacquetLengthWitness_of_coatom_coordinates` derives the
numeric bound from these coordinates and applies
`hasRepresentedJacquetLengthWitness_of_geometricBudget`. That existing result
supplies compact-limit radicals over the nonarchimedean local field and
computes actual Jacquet lengths from the geometric gluings.
`induced_repLength_le_two_of_coatom_coordinates` then applies the exact
detecting-family length criterion. Neither corollary assumes finite length
of the induction.

The provenance is internal: finite sigma counting and double-coset
equivalence injectivity are combined with the proved intrinsic coatom count
and represented geometric-budget reduction. This unit supplies no
unconditional actual geometric lemma, finite family construction, root
comparison, support detection theorem, or unitarizable constituent. Those
remain required for the host's closed maximal-Levi theorem.
