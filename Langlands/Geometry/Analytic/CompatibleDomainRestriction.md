# Compatible strong maps on actual original-chart domains

This module constructs domain restriction in the category of actual compatible
strong atlas morphisms. Its input algebras, charts and bounded maps are the
existing concrete affinoid atlas data. It also constructs the diagram of actual
domain presentations and proves naturality for every nested source and target
pair.

The original source is Berkovich, *Etale cohomology for non-Archimedean analytic
spaces* (1993), Definitions 1.2.7 and 1.2.9, printed pp.18–19 / PDF pp.15–16,
and Definition 1.3.1 with its following paragraph, printed p.23 / PDF p.20.
The registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Definition 1.2.7 requires maps for all admissible chart pairs, and Definition
1.2.9 requires the affinoid-domain property for all such pairs. The paragraph
following Definition 1.3.1 equips a domain with its contained affinoid charts
and defines its canonical inclusion. This module supplies derived construction
obligations for these conventions within the implemented original-chart domain
family. Its two-domain restriction has the explicit chart-containment premise
described below; it does not assert the source's unrestricted analytic-category
factorization property.

For a strong map `f : StrongHom A B`, subsets `S` and `T`, and
`f.baseMap '' S ⊆ T`, `domainBaseMap` is the given continuous map restricted to
the induced subspaces. `domainBaseMap_admissible_iff` proves that admissibility
of two contained charts is exactly admissibility of their original indices.
`HasDomainTargets` says that each original source chart contained in `S` has
an admissible original target chart contained in `T`. This is a condition on
the supplied map and chart ranges. It supplies indices, not new bounded maps,
restrictions, or an assumed factorization.

The module imports `OriginalDomainStrongRestriction` and reuses its existing
`StrongHom.restrictDomains` on the bundled domains `⟨S, hS⟩` and `⟨T, hT⟩`.
`HasDomainTargets` is definitionally the existing `MapsOriginalDomainCharts`
condition for those bundles. No second raw restriction or identically named
raw lemma is introduced. The existing construction retains the presented
algebra at every contained chart and uses `f.pullback` for every admissible
pair; its `restrictDomains_pullback` identifies the entire bounded algebra
homomorphism by literal equality. The existing
`restrictDomains_chartImageLocus` identifies the two spectrum loci in the
same original target algebra, and `IsQuasiIso.restrictDomains` proves the
full quasi-isomorphism property when `f.baseMap '' S = T`. That proof restricts
the ambient homeomorphism and retains the full all-admissible-pair
affinoid-domain property. These are imported results rather than new
constructions in this module.

`HasCoherentPullbacks.restrictDomains` proves the full coefficient-test law
for that existing raw restriction by forgetting the containment proof on
every source, target and common test chart. Its quantified coefficient
algebra, coefficient map and factoring bounded map are unchanged. The
`domainBaseMap` admissibility equivalence applies definitionally to this
raw restriction: both continuous maps have the same underlying function.
The explicit image-containment premise is retained in the set-based
compatible interface, although the containing-chart condition already
implies it for an original-chart domain.

`CompatibleStrongHom.restrictDomains` packages the preceding map using the
proved equivalence between complete coefficient coherence and the original
local compatibility condition. `restrictSubspace` supplies source-only
restriction without a target-domain premise. It similarly preserves all
original bounded maps and their compatibility.

`subspaceCompatibleInclusion` restricts the identity map to the source domain.
`subspaceCompatibleMap` uses that same identity family for any inclusion of
two original-chart domains. The identity and composition laws are equalities
of complete compatible morphisms. For composition, the proof chooses the same
original chart at each stage, computes the composite by the existing
`comp_pullback` theorem, and uses the original restriction identity.
`subspaceCompatibleMap_inclusion` proves the corresponding compatibility with
the ambient inclusion by the same bounded-map argument.

`originalCompatibleDomainFunctor` sends every actual original-chart domain to
its constructed subspace presentation in `CompatibleAtlasPresentation` and
sends each inclusion to `subspaceCompatibleMap`. The preceding laws prove its
functor laws. `originalCompatibleDomainCocone` consists of the actual compatible
inclusions into `A`; its naturality follows from the proved inclusion law. No
colimit assertion is made.

Finally, `CompatibleStrongHom.restrictDomains_naturality` proves the commuting
rectangle for any nested domains `S ⊆ S'` and `T ⊆ T'` satisfying the respective
image and target-chart conditions. The proof chooses an admissible target
chart for the smaller source chart, lifts those same original indices to the
larger domains, and computes both composites. The two bounded composites
reduce to the original pullback with identity restrictions on either side.
Compatible-map extensionality then gives equality of the entire morphisms,
not only equality of their continuous maps.

The coefficient field is complete and nonarchimedean with no nontrivial
valuation assumption. Coefficient, ambient and chart-index universes remain
independent. The existing presented affinoid algebras may be zero or nonreduced.
This module does not prove arbitrary analytic-domain factorization, maximal
atlas recognition, etale sites or structure-sheaf comparison. It uses neither
the special-set intersection statement nor closed-ideal effectiveness.
