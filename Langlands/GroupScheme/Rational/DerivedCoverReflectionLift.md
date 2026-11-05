# Contracting-point lifts from actual relative-root reflections

This internal extension of `DerivedCoverUnipotentLift` works over an arbitrary
field `k : Type u`. Let `i : T → G` be a maximal split torus in a connected
reductive group, and let `π : C → D` be a supplied simply connected cover of
the supplied actual derived subgroup `d : D → G`.

For any cocharacter `ν` of `T`, every rational point of the dynamic contracting
subgroup `U_G(ν)` lifts through the literal composite `π ≫ d`, provided either
of these actual reflection inputs is supplied:

- Each actual relative root has an `IsRelativeReflection` in
  `relativeWeylGroup i`.
- Integral `RelativeRootReflectionData i` are supplied.

Neither result assumes `HasRelativeRootSystem i`, generation of the rational
normalizer quotient by reflections, or a comparison with an abstract Weyl
group. The reflection input itself remains a premise.

The existing unconditional theorem
`IsConnectedReductive.finite_relativeWeylGroup` makes the actual quotient
`N_G(T)(k)/Z_G(T)(k)` finite. Thus its integral cocharacter sum is available
without a root-system realization. For the first reflection input, the
existing `relativeWeylCocharacterSum_mem_centralCocharacters` proves centrality
on every test scheme.

For integral reflection data `R`, `R.action` and `R.pair_self` show that the
chosen normalizing representative sends its root to its negative. Pairing
invariance and fixedness of the Weyl sum then give an integer equal to its
negative; that integer must be zero. This is
`RelativeRootReflectionData.latticePairing_weylSum_eq_zero`.
`rootAnnihilatorCentrality` gives
`RelativeRootReflectionData.weylSum_mem_centralCocharacters`. These two
intermediate results need only a finite actual Weyl group, the supplied
integral reflection data, and the indicated smooth connected affine and
split-torus hypotheses for centrality.

The existing derived Weyl-correction construction now applies. It factors
`|W|ν − ∑w wν` through the actual derived subgroup. The central Weyl sum and
positive integer `|W|` preserve the entire dynamic contracting subgroup.
The central-isogeny lifting theorem for `C → D` therefore gives the desired
rational lifts. The two `exists_derivedCover_lift_of_mem_unipotent` variants
record exact point equations, and the corresponding
`unipotentPoints_le_derivedCoverImage` variants record subgroup inclusions.

`Dynamic.derivedCoverUnipotentPointLiftOfReflections` selects an actual point
of `C(k)` over each contracting rational point. Its `_comp` theorem states
that mapping this chosen point under `rationalPoints.map (π ≫ d)` recovers
the original point. This is a set-theoretic selection; it does not assert
that the selection is a group homomorphism.

The provenance is internal: the unit combines the named published Library
results and the displayed elementary pairing argument. It is a prerequisite
for the minimal-Levi product target associated with Kaletha–Prasad,
Fact 2.6.22. It leaves actual reflection existence and the other structural
inputs to that full product theorem outstanding. It imposes no restriction
on characteristic, perfectness, valuation, topology, or universe.
