# Renard II.2.2: germ supports and compact-section carriers

Worker 865 implemented the definitions and elementary proofs. Worker 6 supplied
the source audit, interface specification and subtype compactness route.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.2, printed pp.37–38 /
PDF pp.43–44. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both complete PDF pages were read. The supplementary registered 2010-edition
*Corrections et compléments*, `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3 were also read; these pages do not change the support definition.

On printed p.37 the source assumes a basis sheaf and defines a section's support
to be the points of its domain with nonzero stalk value. On printed p.38 it
defines `F_c(U)` as the set of sections with compact support, using the earlier
identification of a sheaf with its germ-section sheaf. Here the definitions use
the actual locally represented carrier `GermSections F U` imported from
`Langlands.Sheaf.Renard.GermSections`. Accepting an arbitrary `RawPresheaf F`
is an internal extension of the source's sheaf input. It does not identify
original presheaf sections with germ sections or assume the canonical-unit
comparison for sheaves.

`germSupport s : Set U` is literally `{x | s.val x ≠ 0}` in the subtype
topology of the domain open. `germSupportAmbient s : Set X` is its image under
the actual inclusion `Subtype.val : U → X`. The membership formulas expose
both descriptions, and the ambient image is proved to lie in `U`. Neither
support is defined by taking a closure. The two sets belong to different
topological spaces; relative closedness would not assert ambient closedness
when `U` is an arbitrary open.

The zero and negation laws follow from the existing pointwise group operations
and the corresponding group identities in each original stalk. For addition,
if the first value is zero, a nonzero sum forces the second value to be nonzero;
otherwise the first value already witnesses membership in the union. Taking
actual image witnesses gives all three ambient consequences. These are
elementary intrinsic consequences of the source definition, rather than
additional source propositions.

`germSupport_restriction` is a definitional equality with the preimage under
`x ↦ ⟨x.val, h x.property⟩` for an actual inclusion `h : U ≤ V`.
`germSupportAmbient_restriction` proves the ambient equality with the original
ambient support intersected with `U`, by transporting subtype image witnesses
in both directions. Both use the imported `germRestriction` unchanged.
`germSupport_map_subset` uses the actual pointwise `rawStalkMap` defining
`germSectionsMap`: a zero input has zero output because this is an additive
map. Its ambient consequence again transports image witnesses. No injectivity
or monomorphism hypothesis occurs.

`compactGermSectionsSet F U` is exactly the set of sections whose relative
support is compact, and `CompactGermSections F U` is its subtype carrier.
`compactGermSectionsInclusion` is the actual injective function `Subtype.val`
into `GermSections F U`. The membership formula and the subtype's support
compactness theorem expose the same predicate. `isCompact_germSupport_iff`
specializes Mathlib's `Subtype.isCompact_iff` to identify compactness of the
relative support with compactness of its ambient image. This equivalence
requires no Hausdorff hypothesis. Zero belongs to the set, and the relative
and ambient support formulas include the empty domain.

Space universe `u` and original-section universe `v` remain independent.
The section and compact-section carriers live in `max u v`. No Hausdorffness,
local compactness, total disconnectedness, intersection closure of the chosen
basis, empty basis member, nonempty domain or nonzero stalk is required.
All fibers, operations, restrictions and induced stalk maps are the imported
ones; no replacement carrier or comparison hypothesis is introduced.

The existing ordinary all-open module construction is
`Langlands.Sheaf.CompactSupport` in `Langlands/Sheaf/CompactSupport.lean`.
Its `support` uses Mathlib colimit stalks for global sections of an all-open
`ModuleCat` presheaf; it proves closedness and constructs a compact-section
submodule and functor. Its space, coefficient and module universes are coupled.
No checked comparison identifies its stalks or compact-section objects with
the present arbitrary-basis, independent-universe germ model. This module
neither imports nor asserts that comparison.

The source's relative-closedness proposition remains a later statement and
proof over this interface. Compact-section additive subgroup and functor
constructions require that result: support containment in a compact set alone
does not imply compactness of the smaller support. The canonical-unit
identification, clopen zero extension, II.2.4 compact-open exhaustion and
locally constant scalar-sheaf comparison are separate units. In particular,
this module supplies no restriction map on compact sections for arbitrary
open inclusions.
