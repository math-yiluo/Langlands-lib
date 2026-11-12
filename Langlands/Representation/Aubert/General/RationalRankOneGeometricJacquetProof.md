# The rank-one geometric Jacquet computation on actual rational points

Author: Worker 124.

This module proves

```text
Langlands.Aubert.General.RationalPointFamily.rationalRankOneGeometricJacquet :
  Langlands.Aubert.General.RationalPointFamily.RationalRankOneGeometricJacquetStatement.{u,v}
```

The theorem has no parameters outside that published proposition. Its independent
universes `u` and `v`, actual rational-point group and canonical `pointTopology`,
literal `SimpleRoot i ν` labels, actual standard parabolic/Levi/unipotent families,
normalized induction/Jacquet functors and every displayed structural and Coxeter
premise are preserved. The field may have positive characteristic; the connected
reductive group may be nonsplit or non-quasisplit. Carriers have universe
`max (u + 1) v`. The target and its imported Lean/Markdown pairs are unchanged.

For maximal proper `J`, arbitrary smooth inside-Levi cuspidal `σ`, and every
supplied lift `n` of `longestRep actual J` with normalization witness `hself`, the
result constructs actual intertwining maps in the short exact sequence

```text
0 → (conjugationFunctor n⁻¹ _).obj σ → r_J(i_J σ) → σ → 0
```

and proves `IsZero (r_K(i_J σ))` for every `K ≠ univ`, `K ≠ J`.
The inverse conjugate acts by `x ↦ σ(n * x * n⁻¹)`. No irreducibility,
finite length, admissibility, reducibility, supplied filtration, double-coset
data or grade-isomorphism premise is added. The proof never identifies a
Grothendieck-class equality with an actual representation isomorphism.

## Constructing the actual filtration

The supporting theorem `rationalMaximalSourceGeometricFiltration` proves the
whole `RationalMaximalSourceGeometricFiltrationStatement.{u,v}`. It introduces
that proposition's actual data and invokes
`pointGeometricObjectFiltrationOfEpsilonBalance`. That construction supplies
all actual orbit, representative, decomposition, filtration and grade data.
Its only additional epsilon premise is discharged by the imported theorem
`geometricEpsilon_mul_eq_one`, applied with the original standard semidirect
decompositions, the given closed radicals/Levis, the derived
`isClosed_standard_parabolic` and `continuous_standard_projection`.
Thus no normalization or orbit-comparison theorem remains assumed.

More explicitly, the construction uses the unconditional
`GroupScheme.standardParabolicPointsStatement_proof`, the actual
`minimalOrbitOrdering` and closed-quotient topology to obtain a finite
bijection with the minimal Weyl double-coset representatives. For a self
composite, its identity-class lift lies in the actual Levi, so its orbit is the
closed singleton identity coset. `OrderedDoubleCosets.closedOrbitLast` puts it
last before constructing the support filtration and preserves open initial
unions. The source and target semidirect decompositions are derived from
`pointSourceIntersectionIdentities` and
`geometricIntersectionDecompositions_of_pointSource`.
`jacquetSupportFiltration` is then evaluated at `σ`, and
`jacquetSupportGeometricTermIso` supplies each actual normalized grade.
Projection continuity and compact-subgroup limits for the radicals are proved
by their standard-family transport theorems. This argument actually handles
all source/target subsets and arbitrary smooth inducing objects; the supporting
universal proposition requests only maximal sources and proper targets.

`geometricEpsilon_mul_eq_one`, from Worker 4021's
[RationalGeometricEpsilonBalance](RationalGeometricEpsilonBalance.md), cancels
both original Haar corrections on the entire literal common Levi. It factors
them into five actual positive Haar moduli, realizes the common Levi as a
dynamic centralizer of a dominant cocharacter combination and derives character
restriction injectivity from the published Levi split-component, split-component
and central split-torus character theorems. It then applies
`centralizingHaarCharacter_correctionProduct_eq_one_of_characterRestrict_injective`
and transports its identity to the actual nested point subgroup. No input
character is assumed trivial to erase a Haar correction, and the source
positive and Jacquet inverse half-moduli retain their original signs.

## Collapsing the filtration on cuspidal data

The final theorem applies
`rationalRankOneGeometricJacquetOfMaximalSourceFiltration` to that proved
filtration statement. The actual normalization witness and existing structural
and actual Levi Weyl premises first imply `associatedSubset actual J = J` by
`pointAssociatedSubset_eq_of_normalizing_longestLift`.

Full source intersection at a minimal representative gives
`MapsIntoSimple`. Conjugation injects its source simple labels into the target
labels. Maximality of the source and properness of the target force equal
cardinalities. `coatom_simpleSurvivor_classification` therefore leaves only the
identity pair or the inverse-longest pair with associated target. This proves
that every geometric term at a different proper target has proper source
intersection. Inside-Levi cuspidality kills its source Jacquet module, hence
the whole normalized geometric term. Actual grade isomorphisms and
`objectRepFiltrationSubsingleton` give zero for the ambient other-target
Jacquet object. No finiteness condition on `σ` is used.

At `J`, every class except `1` and `(longestRep actual J)⁻¹` similarly vanishes.
These classes differ because the longest representative's ascent set is the
associated subset, and `J` is proper. Bijective enumeration places the
inverse-longest class at a unique prefix index, since the identity is last.
`pointRankOneInverseLongestTermIso` identifies that grade with the required
inverse conjugate for the exact supplied lift `n`, and
`pointGeometricTermIdentityClassIso` identifies the last grade with `σ` for
every identity-class lift. The centralizer ambiguity changes the term by an
inner-source-Levi isomorphism; no elementwise equality of conjugation maps is
claimed. `smooth_shortExact_of_last_and_single_prefix` identifies the
penultimate subrepresentation with the one surviving prefix grade and composes
its actual inclusion and the last actual quotient map with these isomorphisms.
Their injectivity, surjectivity and range/kernel equality give the specified
short exact sequence in the required direction. It is not assumed split.

An empty simple-root type has no maximal standard subset, so both the
filtration specialization and rank-one result are vacuous there. No positive-rank
hypothesis is introduced.

## Original-source correspondence

Casselman, *Introduction to the theory of admissible representations of p-adic
reductive groups*, draft 1 May 1995, §7.1, printed/PDF p.67, states in Lemma
7.1.1(a) the self-dual sequence with half-modulus twists on the unnormalized
Jacquet module and cites the geometric lemma, 6.3.5 (printed/PDF p.59).
The present sequence uses normalized Jacquet restriction, so those endpoint
half-modulus twists are absent. Casselman's §7.1 assumes irreducibility and
absolute cuspidality. Here the general smooth geometric-filtration construction
and the actual proper restricted Jacquet vanishing suffice, so irreducibility
and finite length are not added. Aubert 1995, proof of Corollaire 1.10(b),
printed p.2183 / PDF p.5, cites this computation and records vanishing at the
other proper standard subsets; her constituent labeling is not used in this
proof of the induced object's sequence.

Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 version,
VI.5.1, printed pp.161–163 / PDF pp.167–169, provides the normalized all-smooth
geometric lemma and support-filtration formulation. His orbit representative
`z` is `n⁻¹` in our convention: source intersections lie in `L_J` and target
intersections in `L_I`, exactly as in `geometricTermFunctor`. The Lean route
constructs this actual filtration using the published Mackey support and
normalized orbit comparisons, then collapses it by the finite Coxeter
classification. It does not rely on Aubert Proposition 3.2 or its defective
original application.

## Declaration-level dependencies and retained scope

The two direct final-proof dependencies are
`rationalRankOneGeometricJacquetOfMaximalSourceFiltration` and the supporting
`rationalMaximalSourceGeometricFiltration`. The latter directly invokes
`pointGeometricObjectFiltrationOfEpsilonBalance`, `geometricEpsilon_mul_eq_one`,
`isClosed_standard_parabolic` and `continuous_standard_projection`.
Their detailed construction routes are documented in
[RationalGeometricObjectFiltrationConstruction](RationalGeometricObjectFiltrationConstruction.md),
[RationalRankOneGeometricFiltrationAssembly](RationalRankOneGeometricFiltrationAssembly.md),
[RationalRankOneGeometricTerms](RationalRankOneGeometricTerms.md),
[ClosedOrbitLast](../../Geometric/ClosedOrbitLast.md),
[LastAndSinglePrefixSequence](../../Filtration/LastAndSinglePrefixSequence.md)
and [RationalGeometricEpsilonBalance](RationalGeometricEpsilonBalance.md).

The transitive geometric-lemma route is the actual support/Mackey filtration
and the normalized orbit-grade comparison:
`jacquetSupportFiltration`, `jacquetSupportGeometricTermIso`,
`jacquetSupportOrbitIso`, `orbitPieceCoinvariantsIso`,
`geometricNormalizedCompactSourceRepIso`,
`geometricNormalizedCompactActualNatIso`, `geometricEpsilonCompactTermIso`
and `compactSmoothIso`. All the extra closedness, continuity, radical
compact-limit, orbit finiteness, target quotient compactness and epsilon
premises used by that route are discharged from the displayed target data
and the named published structural proofs. The generic finite-filtration
helpers supply actual quotient comparisons and exactness, not representation
classification results.

No adjointness, cuspidal-support theorem, character independence of
representations or Langlands classification is used by these proof bodies or
the documented dependency routes. The epsilon proof's injectivity concerns
algebraic rational characters of a connected reductive centralizer; it is not
independence of irreducible representation characters. The imported closure
contains other targets and conditional constituent, support and finite-length
assemblies. Those imports do not invoke their unproved hypotheses. In
particular the host module's length-two and cuspidal-support-detection
implication is not used. The result is conditional precisely on the original
visible structural and Coxeter premises, and establishes neither their global
discharge nor the separate length-two and constituent-pattern targets.
