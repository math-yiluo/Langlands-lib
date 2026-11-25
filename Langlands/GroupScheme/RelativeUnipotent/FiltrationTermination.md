# Finite termination of relative vector-bundle filtrations

These are internal, derived helpers for the finite-series consequence of
Conrad, *Reductive group schemes* (2014), Theorem 5.4.3, p.174 and proof
pp.175–177. They do not construct the filtration promised by that theorem.

`range_id_eq_bot_of_geometricFibres` applies over an arbitrary scheme. A
smooth group whose geometric fibres are trivial on all tests is itself
trivial on all tests. The proof compares the base changes of its identity
section with the identity maps of the geometric fibres using represented
subgroup functors. These maps are isomorphisms, so the published geometric
fibre isomorphism criterion makes the identity section an isomorphism over
the original base. Its range is the identity subgroup, which therefore is
the range of the group's identity map.

`hasVectorBundleSeries_of_segment` takes actual groups indexed by natural
numbers, closed smooth normal step inclusions and represented fppf quotients
that satisfy the unchanged `IsVectorBundleAdditive` predicate. If the last
term of a finite segment is trivial on all tests, induction on the segment
length constructs `HasVectorBundleSeries` for its first term.

`hasFiniteVectorBundleSeries_of_geometric_termination` combines these facts:
a supplied descending filtration whose term at a common index is smooth
and has trivial geometric fibres gives a finite vector-bundle series for
its zeroth term. No noetherian, connectedness, nonempty-base or constant-rank
hypothesis is imposed. Filtration construction and a common termination
index remain inputs to this helper.

`seriesWitnessOfGeometricTermination` is the corresponding data constructor.
It returns the supplied common index together with the finite-series proof
at that length, as a subtype of the natural numbers. It uses the segment
induction and geometric triviality reflection just described; it makes no
choice of a new filtration or of a termination index.
