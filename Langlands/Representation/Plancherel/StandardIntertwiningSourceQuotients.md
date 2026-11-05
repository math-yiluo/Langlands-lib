# Actual quotient measures at the common ambient source scale

This internal derived construction applies the proved compatible quotient
measure existence theorem to the exact intrinsic source Haar measures on
the actual intersection and nested subgroup carriers. Its motivating source
is Waldspurger (2003), `waldspurger-2003-plancherel`, I.1, printed p.240 /
PDF page 6 (index 5), for normalization at one fixed special maximal compact;
IV.1, printed p.279 / PDF page 45, for the ordered complementary-unipotent
integral; and IV.1(12), printed p.283 / PDF page 49, for the later rational
composition identity. The measure selectors and conditional composition
specialization are internal deductions. These passages are not asserted to
prove the supplied compact-open covers or the general reductive geometry.

The measure constructors require a Hausdorff locally compact topological
group `G`, a supplied compact open `Q`, the displayed closed original
subgroups and Borel measurable structures on each actual carrier and
quotient. `sourceSubgroupHaar_rightInvariant_of_cover` applies the existing
compact-open-cover unimodularity result to the intrinsic
`subgroupCompactOpenHaar Q hQ B hB`. Its cover consists of compact open
subgroups of the original `B` containing each element, not just a
neighborhood basis at the identity. Closedness supplies the closed
embedding into `G`; no ambient measure is restricted to `B`.

For two original closed subgroups `A` and `B`, `sourceQuotientMeasure`
constructs a measure on the actual possibly nonnormal left quotient
`(A.subgroupOf B) \ B`. Covers of `A` and `B` give right invariance of,
respectively, `sourceIntersectionHaar Q hQ A B hA hB` and
`subgroupCompactOpenHaar Q hQ B hB`. The first uses the already proved
intersection-to-source cover inheritance; the second uses the new
original-subgroup lemma. Local compactness of `B` follows from closedness.
The intersection is closed in `B` by inverse image of the original closed
`A` under subtype inclusion.

The definition selects a quotient only from the proved
`QuotientIntegration.compatibleMeasureExists` for those exact two measures.
`sourceQuotientMeasure_isCompatible` is its choice specification. It gives
nonzero mass, regularity, preservation by the actual right quotient action,
integrability of quotient averages of compactly supported continuous
complex functions, and their Weil integral formula. The module also
exports regularity and nonzero consequences. A local instance binder makes
the derived kernel right-invariance proof available in the compatibility
type; it adds no measure assumption.

For the supplied `OrderedSubgroupFactorization D`,
`sourceNestedQuotientMeasure` similarly constructs the actual quotient of
`U₁.subgroupOf U₂` by
`(U₀.subgroupOf U₂).subgroupOf (U₁.subgroupOf U₂)`. Its ambient measure is
exactly `sourceIntersectionHaar Q hQ U₁ U₂ hU₁ hU₂`; its kernel measure is
exactly `D.sourceNestedKernelHaar Q hQ hU₀ hU₂`. Covers of the original `U₁`
and `U₀` give their right invariance. The closed intersection embedding
gives local compactness of the ambient carrier. Two subtype inverse images
of the original closed `U₀` give closedness of its nested kernel. Selection
and the theorem `sourceNestedQuotientMeasure_isCompatible` then use the
same proved existence theorem. Regularity and nonzero mass are exported
here too. No comparison of differently normalized quotient measures is
needed in either construction.

`comp_hasIntegral_at_sourceQuotients` adds the predecessor's
nonarchimedean and ambient second-countability assumptions, the actual
ordered subgroup charts, the three unchanged local Cartesian image
identities, and covers of the original `U₀`, `U₁`, `U₂`, `V`, `W`.
The cover of `U₂` is an additional hypothesis compared with the predecessor
that accepted supplied compatible quotients: it proves ambient right
invariance needed to construct the two endpoint quotients. A cover of
the full ambient `G` is not required. All source measures and compact opens
still use the same supplied `Q`. The charts are literal ordered
multiplication homeomorphisms, with no direct-product group assertion.

The first `HasIntegral` witness `hf` is stated for
`sourceQuotientMeasure` on `(U₀ intersect U₁) \ U₁` and represents its
output by evaluation of the actual induced section `F`. The second witness
`hF` uses that same `F` and the chosen quotient on
`(U₁ intersect U₂) \ U₂`, with output the same function `J`. Ordered scalar
integrability against every smooth functional on the original carrier,
with the original source Haar measures on `V` and `W`, remains a hypothesis.
The conclusion is the actual direct `HasIntegral` relation for `f` and `J`
at the constructed quotient on `(U₀ intersect U₂) \ U₂`.

The proof constructs the nested quotient and uses the three ordinary
quotient selectors, supplies their four proved compatibility properties,
and applies `comp_hasIntegral_at_sourceScale_of_covers` with unchanged
local geometries, `hf`, `hF`, `F`, `J` and scalar integrability. Thus the
quotient choices precede the witnesses in the theorem's types. The proof
never substitutes a new quotient for one already carrying an integral
witness and introduces no residual scalar. Its dependent instance proofs
agree by proof irrelevance.

The representation is the canonical `SmoothRep` of the common Levi, with
independent ambient-group and representation-carrier universes. No
irreducibility of parabolic induction, splitness or field characteristic
restriction is imposed. The genuine covers, source special compact,
reductive realizations of the charts and local image identities, integral
convergence, original-carrier representability and rational continuation
remain application obligations. Quotient existence at this supplied source
scale is proved rather than assumed. No whole-task Plancherel completion
condition is closed by this construction.
