# The arithmetic rank-one height input and its minimum/torus consequences

This derived interface isolates the arithmetic height assertion still needed for
general rank-one chamber reduction. It uses actual group-scheme rational and
adelic points and the published normalized primitive-vector height. Its
rank-one assertion is a proposition definition and remains unproved here.

`HasUniformNormOneRationalOrbitHeightBound F G rho v` means that one real
constant `C > 0` works for every ambient norm-one adelic point: some actual
rational right translate has selected-vector height at most `C`.
`IsRationalOrbitHeightApproximateMinimum` records the inequality
`H(g) ≤ c H(g q)` for every actual rational point `q`. These comparisons use
the full rational group, rather than a parabolic or a preceding intersection.

The first theorem bounds each such approximate minimum by `c C` when
`c ≥ 0`. It applies its minimum inequality to the small rational translate
given by the arithmetic bound. Conversely, for a nonzero rational vector,
bounding all exact minima is equivalent to the uniform rational-orbit bound.
The reverse implication uses the published actual rational-subgroup minimum
construction with subgroup equal to the whole rational group; its selected
translate remains in the ambient norm-one group by the product formula.
Existence of a minimum alone supplies no uniform bound.

`orbitHeight_unipotent_mul_normOne_mul_torus` computes the height of the ordered
actual product `u m s`. The representation must preserve the selected coordinate
line on each of the three specified subgroup schemes, the first group must be
unipotent, and `m` must be in the intrinsic norm-one group of the second group.
The rightmost torus point scales height by its actual line-character norm.
The norm-one factor has line-character norm one. The unipotent line stabilizer
fixes the selected vector, so its height equals the identity height.
These three identities give exactly the torus point's height. This argument
does not transfer a minimum inequality through an arbitrary fixed right factor.

The following theorem applies this identity to any family of torus coordinates
of norm-one approximate minima with these actual factors. A supplied uniform
rational-orbit bound then gives a uniform torus-line height bound `c C`, for
every fixed positive `c`. The factorization, preservation and minimum premises
are explicit. No coordinate decomposition or arithmetic bound is constructed
by this implication.

`RankOneParabolicRationalOrbitHeightBoundStatement` quantifies over arbitrary
number fields and universes, affine finite-type connected reductive group
schemes, actual maximal split tori and generic cocharacters whose set of
simple relative roots is a singleton. Every actual finite-coordinate
representation whose exact selected-line stabilizer is the empty-index
standard parabolic must have the uniform rational-orbit bound on ambient
norm-one points. The exact stabilizer uses all relative scheme tests and unit
scalars, as in the published actual Chevalley interface. The group need not
be split, and no compactness, Iwasawa, fundamental-set or chamber-coverage
premise is supplied. The assertion concerns positive semisimple relative rank
one; it does not require the maximal split torus itself to have dimension one.

The provenance is the published rational-orbit minimum construction,
unipotent coordinate-line fixedness and exact line-character height identities,
combined with the actual rank-one parabolic-line construction. This is an
internal arithmetic prerequisite formulation, not a claimed quotation or proof
of a source theorem. It does not prove the general chamber-reduction target.
