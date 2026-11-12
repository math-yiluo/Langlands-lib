# Renard II.3.13: the categorical center and conjugation invariance

This statement unit covers the Corollary and its proof, including
(II.3.13.2)–(II.3.13.3), in Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.3.13, printed pp.55–56 / PDF pp.61–62.
The group is an arbitrary Hausdorff locally compact totally disconnected
topological group, with its Borel structure and a left Haar measure.
There is no countability or unimodularity restriction.

The namespace is
`Langlands.HarmonicAnalysis.Distribution.RenardCenter`.
The unit reuses the original full dual, its already constructed essential
compactness submodules, the actual compact convolution and both full Hecke
actions. Conjugation invariance is exactly the published
`Distribution.IsConjugationInvariant`, invariance under pushforward by
every actual inner homeomorphism. There is no replacement definition of
conjugation invariance or of a categorical center.

`TraceCondition μ T` is (II.3.13.2): for every scalar test `f` and Hecke
distribution `h`, `T(f * h) = T(h * f)`. The two scalar convolutions are
the published `rightConvolveTest` and `leftConvolveTest`, represented by
tests with exactly those pointwise values. This retains the distinction
between scalar test/distribution convolution and the left-Haar product
of two bare density functions on a nonunimodular group.

`TranslationCondition T` is the source's equivalent Dirac-translation
identity: `T(leftTranslate g f) = T(rightTranslate g⁻¹ f)`.
`SandwichTraceCondition T` records (II.3.13.3), using the actual compact
distribution `e_K * dirac g * e_K`. It includes all four printed local-unit
conditions on `f`, `dirac g * f` and `f * dirac g`. The products with these
scalar tests again use the original scalar convolutions and actual test
witnesses. `CriteriaStatement` states equivalence of conjugation
invariance with each of these three conditions on the full algebraic dual.
The source proves the equivalences in its center argument; their
formulation for any distribution is the same local-test argument, an
explicit internal extraction of that proof.

`CentralitySpecification μ pr` states that the center for the specified
right product is the commutant of the actual Hecke density range, that
this is equivalent to conjugation invariance, and that such a right
essentially compact distribution is automatically two-sided essentially
compact. This is the first paragraph of the Corollary's proof.

The categorical object in `CategoricalComparisonSpecification` is
`Langlands.Algebra.NondegenerateModuleCenter (HeckeAlgebra μ)`,
definitionally `CatCenter` of the category of nondegenerate original
Hecke modules. Its elements are actual natural transformations of the
identity, with original module intertwiners as components, and its ring
is the published named `NondegenerateModuleCenter.ring`.
For `G : Type uG`, the module-carrier universe is explicitly
`max uG uM`, where `uM` is arbitrary. Thus it contains the Hecke carrier
universe, as needed for reconstruction on the regular module. The target
does not assert the classification for a possibly smaller module universe.

The comparison is a bijection onto the actual subtype of
`essentiallyCompact μ` satisfying the existing conjugation-invariance
predicate. It preserves addition and the specified two-sided convolution
product and sends the categorical identity to the actual `dirac 1`.
It is tied to the actual completion comparison `E` by requiring that
each central transformation is exactly the published
`NondegenerateModuleCenter.fromCommutantRingHom hA x` for a compatible
family `x` whose value is `E T`, with `T` the same underlying distribution.
This equality is an equality of entire natural transformations; in
particular it fixes every module component by the published
compatible-family action. The classification is not replaced by an
arbitrary bijection to a carrier named “center”.

`CategoricalCenterStatement` existentially supplies the right, left and
two-sided products with all their specifications, the actual completion
comparison, the centrality criterion and this categorical comparison.
These are conclusions, not assumed classification hypotheses.
`Statements` conjoins it with `CriteriaStatement`.
No proof is included. The algebra and completion targets are separate
units reused here by their Lean names.
