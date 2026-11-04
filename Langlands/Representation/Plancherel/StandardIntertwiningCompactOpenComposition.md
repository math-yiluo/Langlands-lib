# Common compact-open complements for normalized standard integrals

This is an internal derived construction for the ordered integration in
Waldspurger (2003), IV.1, printed p.279 / PDF p.45, and its role in IV.1(12),
printed p.283 / PDF p.49. It uses supplied ordered charts and displayed
compact-open data. Actual reductive realization, convergence and rational
continuation remain open.

`firstComplementCopiesEquiv` identifies the actual copy of `V` in `U₁`
with its actual nested copy in `U₁ ∩ U₂`. It is the first complement
equivalence followed by the inverse intersection complement equivalence.
It preserves the underlying elements of the ambient group.
`firstCompactComplement B` is the inverse image of the open subgroup `B`
under this continuous group equivalence. It is compact when `B` is compact.

`firstCompactComplement_mass` computes the inverse-transported normalized
factor measure of this open subgroup. Pushforward composition and inverse
equivalence cancellation give exactly the mass of `B` for the normalized
intersection factor before its transport to `V`. No Haar or compactness
assumption is needed for this equality, beyond the displayed Borel structures.

`firstCompactComplement_volume` applies the existing compact-open mass
normalization theorem. It retains the Hausdorff topological ambient group,
the three Haar measures, closedness of the actual nested kernel and
compactness of `S` and `B`. The result is the middle compact-open volume
equal to its kernel volume times the transported first-complement volume.
`firstCompactComplement_mass_one` specializes this to unit mass on `S`
and its kernel. The complement then has unit mass regardless of the
independent seed measure's scale.

`measurePreserving_first_of_unitCompactOpens` takes a compact open `R` in
`U₁` and the local Cartesian product image of its intersection kernel
times `firstCompactComplement B` onto `R`. It assumes unit mass on `R`,
its kernel, `S` and the nested kernel of `S`. It derives closedness of the
nested kernel from closed `U₀`, obtains unit complement mass as above, and
uses `measurePreserving_first_normalized_of_compactOpenMass`. Compactness
of the first complement is proved by transport. Its exact conclusion is

`MeasurePreserving D.first (μI₁₀.prod μV) μU₁`,

where `μV = D.intersectionNormalizedFactor μI₂₁ μH μK S B`.
The first product identity and the first-factor mass comparison are
conclusions, with neither inserted as a premise.

This theorem retains locally compact Hausdorff topological `G`, closed `U₀`
and `U₁`, regular Haar `μU₁`, regular two-sided S-finite Haar `μI₁₀`,
Haar `μI₂₁` and `μH`, regular two-sided S-finite Haar `μK`, regularity
of `μI₁₀.prod μV`, the displayed individual, product and quotient Borel
structures and compatible Weil `ν₁₀`. It uses compactness of `R`, `S`
and `B`, the local image equality and the four unit-mass equalities.
The earlier first-factor theorem derives the required local compactness
and Haar property of the constructed factor.

## Actual integral composition

`comp_hasIntegral_of_unitCompactOpens` combines this first-chart comparison
with the existing locally normalized integral-composition theorem. It
uses the actual independent measures

- `μU₁`, `μU₂` on the original intermediate and target groups;
- `μI₁₀` and `μI₂₁` on the two original intersection kernels;
- `μH`, `μK` on the nested kernel and complement in the middle intersection;
- `μL` on the actual second complement inside `U₂`.

The endpoint kernel is `D.intersectionKernelMeasure μH`; the first
factor is `μV` above; and the second factor is
`μW = D.secondNormalizedFactor μU₂ μI₂₁ μL T C`.
No measure is obtained by restriction of ambient Haar to a subgroup.

The complete setting is a locally compact Hausdorff nonarchimedean group
`G`, closed `U₀`, `U₁`, `U₂`, the original three literal charts,
and all displayed individual, product and quotient Borel structures.
Both `μU₁` and `μU₂` are regular Haar. The measures `μI₁₀`,
`μI₂₁`, `μH`, `μK`, `μL` are regular two-sided S-finite Haar.
The regularity assumptions are those of `μH.prod μK`,
`μI₂₁.prod μL`, `μI₁₀.prod μV` and `μV.prod μW`.
The actual quotient measures `νH`, `ν₁₀`, `ν₂₁`, `ν₂₀` are
compatible Weil measures for their displayed ambient and kernel measures.

The three local product image identities concern, respectively, the
original first chart on `R`, the nested intersection chart on `S`, and
the second chart on `T`. The compact open complements are
`firstCompactComplement B`, `B` and `C`. Compactness of all supplied
compact opens is retained; compactness of the first one is derived.
The four unit-mass premises are exactly those used by the preceding first
comparison. There is no unit-mass premise on `T` or `C`: the second
complement is normalized by its own explicit volume ratio.

For semidirect decompositions with a common Levi, take a canonical
`SmoothRep.{0,uG,uV} ℂ M` and a section `f` of the actual positive
Levi-normalized induction at the first parabolic. Retain an actual first
integral witness represented by a section `F` of the intermediate
induction, a second integral witness with output `J : G → A`, and
`OrderedScalarIntegrable` for `f` and the constructed `μV`, `μW`.
This last condition is absolute scalar product integrability for every
smooth functional at every ambient argument. The conclusion is the actual
direct `HasIntegral` relation with output `J`, on the original carrier.
The ambient-group and representation-carrier universes are independent.

The implemented proof derives the first product normalization using the
unit compact-open comparison, then applies
`comp_hasIntegral_of_localProducts`. That theorem derives the second and
composite product identities from the other local image identities,
derives all three quotient-coordinate normalizations through compatible
Weil integration, and applies smooth weak Fubini in the original order.

None of these results asserts that actual reductive charts or source
compact opens satisfy their premises. Source Haar comparison is reduced
here to four concrete compact-open unit normalizations, whose realization
remains an application obligation. Actual reductive geometry, all
convergence and representability of the two integrals for arbitrary
sections, and rational continuation remain open. No whole-task Plancherel
completion condition is closed.
