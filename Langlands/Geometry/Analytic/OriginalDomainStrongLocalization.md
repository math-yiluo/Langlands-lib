# Full strong maps under original-domain localization

Author: Worker 36.

This derived construction fixes actual indexed affinoid atlas presentations
`A` and `B` over a complete ultrametric normed field. For an original-chart
domain `S` of `A` and an original-chart domain `U` of the constructed atlas
on `S`, it identifies full strong maps into `B` from the ambient-image
presentation of `U` with those from the nested presentation of `U`.
It constructs the identification on continuous maps and every admissible
bounded algebra pullback, proves that it commutes with domain restrictions,
and packages it as a natural isomorphism of presheaves.

The source conventions are Berkovich, *Etale cohomology for non-Archimedean
analytic spaces* (1993), section 1.1, printed p.13 / PDF p.10
(induced subset topology and quasinet), Definition 1.2.3 and
Remark 1.2.4(i), printed p.16 / PDF p.13 (actual affinoid atlases and bounded
restrictions), Definition 1.2.7, printed p.18 / PDF p.15 (full strong maps),
and Definition 1.3.1, printed p.23 / PDF p.20 (contained-chart atlas of a
domain and canonical inclusion). The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
These pages were reread for this unit. The construction is derived for the
published fixed-original-chart domains. It is not a separately numbered
assertion about all domains of a saturated analytic atlas.

The published `subspaceExtend` sends `U` to its actual ambient image
`Subtype.val '' U.carrier`, an original-chart domain below `S`.
`OriginalDomainNested` supplies a homeomorphism from this image to the
nested subtype, an equivalence of the contained original chart indices,
and chosen bounded atlas arrows in both directions. Each corresponding
chart has literally the same original algebra and bounded restrictions.

`StrongHom.toNestedOriginalDomain_admissible_iff` identifies admissibility
after the inverse homeomorphism with admissibility at the corresponding
ambient-image chart. The proof expands both images, using the same
spectrum point. `toNestedOriginalDomain` constructs the full map from the
nested source: it composes the base map with that actual inverse
homeomorphism and takes every bounded pullback from the corresponding
original chart of the given map. Target existence and the chart square
are inherited at that chart. The two-variable restriction equation uses
the published inverse comparison's preservation of chart containment
and the original map's full restriction equation.

`fromNestedOriginalDomain_admissible_iff` and
`fromNestedOriginalDomain` construct the reverse transport in the same way,
using the forward homeomorphism and chart equivalence.
The two `apply` lemmas give the exact point formulas. The two `pullback`
lemmas give equality of entire bounded algebra homomorphisms, with
explicit admissibility transport.

Both roundtrip laws use `ext_of_pullback` to compare complete strong maps.
The homeomorphism and index equivalence insert and forget intermediate
membership proofs. Thus the base maps and all original bounded pullbacks
agree by reduction and proof irrelevance.
`toNestedOriginalDomain_restrict` and
`fromNestedOriginalDomain_restrict` prove that both transports commute
with every inclusion of subspace domains. They use the same full-map
extensionality: source inclusions commute with inserting or forgetting
the intermediate subtype, and every pullback remains the given original
bounded map. `toNestedOriginalDomain_restrictSubspace` proves equality
between transported restriction to the ambient image and successive
actual restrictions first to `S` and then to `U`, including all bounded
pullbacks.

`originalDomainStrongEquiv A B S U` bundles the two transports and their
inverse laws. `originalDomainStrongLocalization A B S` has source
`S.subspaceExtensionFunctor.op` followed by
`A.originalDomainStrongPresheaf B`, and target
`(A.originalDomainPresentation S).originalDomainStrongPresheaf B`.
Its components are the preceding equivalences, viewed as isomorphisms of
types. The full restriction equality proves their naturality.

The target atlas `B` is arbitrary, with no directedness, greatest chart or
reducedness hypothesis. The coefficient, point and chart-index universes
remain independent. Empty domains are allowed. No equality of bounded
algebra maps is inferred from their induced point maps.
This unit constructs transport and a natural isomorphism of presheaves;
arbitrary-cover sheaf descent, general strong composition, atlas extension,
structure sheaves, etale and equivariant sites and the Harris tower remain
separate obligations.
