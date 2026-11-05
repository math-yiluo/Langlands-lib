# Common coefficient support from finitely many fixed-level classes

This derived internal construction proves the converse of the existing generic
support-to-finiteness reduction. Let `G` be a topological group with its Borel
measurable structure and a supplied left Haar measure `μ`, and let `K` be a
compact open subgroup. The group universe `uG` and representation-carrier
universe `uV` remain independent. No admissibility premise is added.

`basisInverseCoefficientSupport μ K hK ρ hρ b` is the union, over all pairs
`i,j` of indices of the supplied basis `b` of the `K`-fixed space, of the
topological supports of

`g ↦ fixedExtension μ ρ hρ K hK (b.coord j) (ρ g⁻¹ (b i))`.

The definition is meaningful without finiteness or compact coefficients. If
the basis index type is finite and `ρ` has compact smooth-dual coefficients,
`isCompact_basisInverseCoefficientSupport` proves this set compact. The
averaged coordinate extensions are smooth dual vectors, so each inverse
coefficient has compact support, and the union is finite.

`support_subset_basisInverseCoefficientSupport` bounds every inverse
coefficient with `K`-fixed vector and `K`-invariant algebraic-dual functional
by this same set. Outside the set, every coordinate of
`P_K (ρ g⁻¹ (b i))` is zero. Extensionality on the basis first makes each
such projected vector zero, then makes the entire linear map
`P_K ∘ ρ g⁻¹` on the fixed space zero. Every `K`-invariant functional is
unchanged by the normalized Hecke projection `P_K`. It therefore vanishes
on `ρ g⁻¹ v` for every `K`-fixed vector `v`. This containment theorem itself
needs neither a finite index type nor compact coefficients.

`exists_compact_fixedLevel_support` applies the published
`finiteDimensional_fixedVectors` theorem to one actual irreducible smooth
representation with compact smooth-dual coefficients. A finite basis then
gives one compact support bound before both coefficient inputs are chosen.

`fixedLevel_support_of_equiv` transports exactly the same support bound
along a representation equivalence, including between independent carrier
universes. It pulls the fixed vector back through the equivalence and pulls
the functional back by composition. The intertwining identity preserves
invariance and the inverse coefficient pointwise.

`hasUniformFixedLevelCoefficientSupport_of_finite_fixedStratum` assumes
finiteness of the actual quotient-class stratum at `K` and proves the existing
`HasUniformFixedLevelCoefficientSupport` predicate. Choose the quotient's
representative of each class in that finite stratum, choose its support bound
as above, and take their finite union. A nonzero tested coefficient implies
that the fixed vector is nonzero, so its representation's class belongs to
the stratum. The actual isomorphism supplied by `ofRep_eq_iff` transports
the chosen representative's bound to this representation. This also covers
the empty stratum and representations with zero fixed space.

`hasUniformFixedLevelCoefficientSupport_of_sandwich` applies the published
`fixedStratum_finite_of_sandwich` with the proved
`sandwichSimpleModuleDimensionBound` and the fields of the supplied actual
`FixedLevelSandwich μ K hK`. Thus sandwich data alone give the existing
common coefficient-support predicate, at the independently fixed carrier
universe. The proof first obtains finite actual classes algebraically; it
does not assume common support to obtain this finiteness.

The provenance is derived rather than a translation of a separate literature
statement: the module combines the Library's finite-dimensional fixed-space,
normalized-projection, representation-equivalence and algebraic finite-class
results with finite unions of compact sets and elementary linear algebra.
It is a supporting unit for the unchanged rational norm-kernel uniform-support
task. Actual reductive Cartan data, simultaneous compact open levels and the
existence of the required sandwich remain separate obligations. The exact
norm-kernel statement and all pairs it imports are unchanged.
