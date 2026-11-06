# Conjugation of the actual compact-normalized subgroup Haar measures

This derived extension concerns Waldspurger's common-compact normalization in
I.1, printed p.240 / PDF p.6, immediately before formulas (2) and Remark (3).
The registered source is `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source assigns each closed algebraic subgroup left Haar measure of mass
one on its intersection with the common special compact. It does not separately
number this transport comparison.

The setting is an arbitrary-universe nonarchimedean local field, in arbitrary
characteristic, and an affine group scheme locally of finite type. Rational
points carry their existing canonical evaluation topology and Borel measurable
space. The separation, local compactness and topological group properties used
here are existing rational-point results. No reductivity, splitness or
quasisplitness assumption is needed.

The imported `RationalSourceGammaConjugation` already supplies
`oppositeCocharacter_conjugate`, the `conjugateCompact` construction and its
membership and compactness results, and the three gamma comparisons
`gamma_eq_of_compactPreserving_conjugation`, `gamma_conjugateCompact` and
`gamma_conjugate_of_mem_compact`. This extension preserves that complete API
and adds no replacement gamma theorem. It also reuses the existing
`GroupScheme.rationalPointsConjHomeomorph G g` directly, with underlying map
`x ↦ g * x * g⁻¹`.

The new `parabolic_conjugation_mem_iff` and `radical_conjugation_mem_iff`
specialize `Dynamic.mem_parabolic_conj` and `Dynamic.mem_unipotent_conj` to
the identity test scheme. The constant point is the original rational point
`g`, so the conjugated cocharacter is literally
`χ ≫ (G.innerIso g).hom`. `parabolicSourceConjugation` and
`radicalSourceConjugation` use the published `subgroupContinuousMulEquiv`
constructor to restrict the existing ambient conjugation isomorphism to
these literal dynamic rational-point subgroups and their subtype topologies.

For compact opens `K` and `K'` whose membership tests correspond under this
conjugation, `measurePreserving_parabolicSourceConjugation` and
`measurePreserving_radicalSourceConjugation` prove exact preservation of
the original `parabolicHaar` and `radicalHaar`. Both are applications of
the published `measurePreserving_sourceSubgroupHaar`: closedness gives
regular subgroup Haar, and mass one on the corresponding compact trace
forces equality with the already defined target measure. There is no free
normalizing scalar and no replacement by ambient restricted measure.

These subgroup equivalences and their measure-preservation results are the
new declarations. The already published gamma comparisons remain available
through the import; their proof is not repeated. Corresponding compact
membership remains an explicit premise, and this extension neither realizes
the source special compact nor proves arbitrary fixed-Levi independence,
the Iwasawa-modulus comparison, convergence or any Plancherel conclusion.
