# Laws for canonical pullback on actual relative cohomology

This module states five laws for the published
`DerivedSections.relativeCohomologyPullback`. Every law quantifies over an
arbitrary universe `u`, every commutative ring object `R`, actual schemes over
`Spec R`, and actual structure-sheaf modules. The laws involving cohomological
degrees cover every `n : ℕ`, including zero. They concern the existing
`relativeCohomology`, defined as the classical right derived functors of
`relativeGlobalSections`.

The provenance is internal: these are the coherence and normalization
obligations of the existing canonical construction, expressed with Mathlib's
actual pullback isomorphisms and the Library's actual section comparison.
They specialize the f-map functoriality framework described in the Stacks
Project, `cohomology.tex`, section *Functoriality of cohomology*, tags
01F7–01FB, lines 2327–2432, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. That registered source is
`stacks-flasque-affine-vanishing-kunneth-a04446e5`. The five displayed Lean
formulas are internal interfaces; the source passage supplies the derived
f-map construction and functoriality in its coefficient data, rather than
these particular scheme-module formulas. The split-retraction formula is
the internal consequence intended from identity and composition.

Write `H_X(n)` for `relativeCohomology X.hom n` and `P(h,M,n)` for the
published `relativeCohomologyPullback h M n`. These abbreviations are only
explanatory prose. The Lean definitions use the actual maps directly and
do not take a candidate pullback family or any cohomological law as input.

For `X : Over (Spec R)` and `M : X.left.Modules`,
`RelativeCohomologyPullbackIdentityStatement` says that `P(𝟙 X,M,n)`
followed by `H_X(n)` of the component at `M` of
`Scheme.Modules.pullbackId X.left` is the identity of `H_X(n)(M)`.
The coefficient transport goes from pullback along the identity to `M`.

For `h : Y ⟶ X` and `k : Z ⟶ Y`,
`RelativeCohomologyPullbackCompositionStatement` says that pullback along
`h`, then along `k`, then `H_Z(n)` of
`(Scheme.Modules.pullbackComp k.left h.left).hom.app M` equals pullback
along `k ≫ h`. Thus the coefficient isomorphism goes from `k^*(h^*M)`
to `(k ≫ h)^*M`, in contravariant order.

For a coefficient morphism `φ : M ⟶ M'`,
`RelativeCohomologyPullbackCoefficientNaturalityStatement` equates
`H_X(n)(φ)` followed by `P(h,M',n)` with `P(h,M,n)` followed by
`H_Y(n)` of the actual morphism `h^*(φ)`. No quasi-coherence or local
freeness is required.

`RelativeCohomologyPullbackDegreeZeroStatement` uses the forward
components of the existing `relativeCohomologyZeroIso` on both schemes.
It says that `P(h,M,0)` followed by the comparison with ordinary sections
on `Y` equals the comparison with ordinary sections on `X` followed by
`relativeGlobalSectionsPullback h M`. The latter is the actual
pullback/pushforward adjunction unit, mapped by relative sections and
followed by `relativePushforwardSectionsIso h`. This fixes the
normalization against the published elementary map.

For a split pair `m : Y ⟶ X`, `j : X ⟶ Y`, with
`w : j ≫ m = 𝟙 X`,
`RelativeCohomologyPullbackSplitRetractionStatement` says that `P(m,M,n)`,
then `P(j,m^*M,n)`, then `H_X(n)` of the forward component of
`relativeCohomologySplitCoefficientIso m j w` is the identity.
The coefficient isomorphism is the published composite of
`pullbackComp j.left m.left`, `pullbackCongr` for the equality of
underlying scheme maps induced by `w`, and `pullbackId X.left`.
Consequently, a future proof of this statement supplies a left inverse
to `P(m,M,n)`, and hence its categorical monomorphism. The statement
itself asserts the explicit retraction equation.

`RelativeCohomologyPullbackLawsStatement` is the conjunction of these
five propositions in the order just described. There are no geometric,
flatness, acyclicity, comparison or vanishing hypotheses. The equation
`w` is the structural splitting condition in the fifth law. This module
defines propositions and proves none of them. It leaves the published
pullback construction, its elementary helpers and all their imports
unchanged.

The statement interface and original explanatory draft were supplied by
Worker 100. This module supplies no proof of the separate vanishing host;
that host's cohomological retraction requires a future exact proof of
these laws.
