# Renard II.2.2: compact germ-section groups and morphisms

Worker 865 implemented the constructions and proofs. Worker 6 supplied the
source audit, concrete successor specification and the compactness proof route.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.2, printed pp.37–38 /
PDF pp.43–44, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both PDF pages were read directly. The supplementary 2010-edition
*Corrections et compléments*, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, was also read; those pages do not change the support convention.
No source-specific public errata note was present at the checked
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` paths.

The source identifies a sheaf with its locally represented germ-section sheaf
before defining `F_c(U)` as the sections with compact support. Its support is
the literal nonzero set in `U`, closed in `U` by the preceding proposition.
This module constructs the additive-group aspect on the existing actual
`GermSections F U` and `CompactGermSections F U` carriers, using the published
relative-closedness proof. The subgroup, explicit induced maps and their laws
are derived consequences of this definition and the II.2.1 pointwise group
and stalk-map construction; the source does not separately print this API.
Allowing arbitrary raw presheaves is an internal extension: their
`GermSections` already consist of locally represented families, and the
imported relative-closedness theorem applies to them.

`isCompact_germSupport_add` applies `IsCompact.of_isClosed_subset` to the
compact union of the two original supports. The sum support is closed by
`rawGermRelativeSupportClosedness` and lies in that union by
`germSupport_add_subset`. These sets all live in the actual domain subtype
`U`. Containment alone would not establish compactness. Negation preserves
the support exactly and zero has empty support. These facts construct
`compactGermSectionSubgroup F U : AddSubgroup (GermSections F U)`, whose
carrier is definitionally `compactGermSectionsSet F U`. Its membership
characterization is exactly `IsCompact (germSupport s)`. The ambient-image
version follows from the existing `isCompact_germSupport_iff`, with the
actual image under `Subtype.val`; no closure or bounding-compact-set
replacement is made.

`compactGermSectionsAddCommGroup` installs the subgroup's inherited
`AddCommGroup` instance on the already published `CompactGermSections F U`
set subtype. It introduces no new section type or transport. The coercion
laws for zero, addition and negation are definitional equalities in
`GermSections F U`; their pointwise laws give literal zero, sum and negation
in the original stalk at each point. `CompactGermSections.ext` is pointwise
extensionality through the two existing subtypes.

`compactGermSectionsInclusionHom` bundles exactly the existing function
`compactGermSectionsInclusion`. Its function equality, section-value and
point-value formulas are definitional, and injectivity reuses the existing
subtype inclusion theorem. The empty-open group is a subsingleton and
every element equals zero. For an empty ambient space the group at every
open is also a subsingleton. These assertions have no nonemptiness premise;
the empty-space proof eliminates a hypothetical point of the domain.

For an actual natural transformation `φ : F ⟶ G`,
`isCompact_germSupport_map` uses the target section's relative closedness
and `germSupport_map_subset` to view its support as a closed subset of the
compact source support. `compactGermSectionsMap φ U` therefore restricts
the existing additive map `germSectionsMap φ U` to the unchanged compact
subtypes. Its underlying section is precisely that germ map, and its value
at `x : U` is `rawStalkMap φ x.val (s.val.val x)`. Zero and addition follow
from the existing additive map. The inclusion-commutation law is equality
of additive homomorphisms, definitionally on their functions. Identity and
composition use subtype extensionality and the published
`germSectionsMap_id` and `germSectionsMap_comp` laws.

Space universe `u` and original-section universe `v` remain independent;
both section carriers live in `max u v`. The topology, chosen basis and
domain open are arbitrary. The construction assumes no Hausdorffness,
local compactness, total disconnectedness, sheaf condition, normalization,
separation, intersection closure or nonempty domain. Normalized objects
and basis sheaves can use these same groups through their actual
underlying raw objects.

Fixed-open categorical packaging is supplied separately in
`Langlands.Sheaf.Renard.CompactGermSectionFunctor`. Original-section
comparison, clopen zero extension, compact-open exhaustion, scalar
structures and exactness remain separate. In particular, no compact-support
restriction map for arbitrary smaller opens is asserted here.
