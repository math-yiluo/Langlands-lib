# Renard II.2.2: fixed-open compact germ-section functors

Worker 865 implemented the functors and their laws. Worker 6 supplied the
source audit and concrete successor specification.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.2, printed pp.37–38 /
PDF pp.43–44, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read directly. The supplementary 2010-edition
*Corrections et compléments*, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.2–3, was also read; those pages do not change the support convention.
No source-specific public errata note was present at the checked
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` paths.

The source defines compactly supported sections after identifying a sheaf
with its locally represented germ-section sheaf. The present functorial
packaging is a derived consequence of this definition and of the existing
germ maps. Its raw-presheaf generality is internal: the existing
`GermSections` carrier already imposes local representability, so its
relative support is closed without a sheaf hypothesis. This module works
on that actual germ model. It assumes no canonical-unit identification
with original sections.

Fix `X : Type u` with its supplied topology, a chosen `B : OpenBasis X`,
and an arbitrary actual open `U : Opens X`. Then
`rawGermSectionsFunctor B U` has source `RawPresheaf.{u,v} B` and target
`AddCommGrpCat.{max u v}`. Its object at `F` is exactly
`AddCommGrpCat.of (GermSections F U)`, and its map at an actual natural
transformation `φ` is the bundled additive homomorphism
`germSectionsMap φ U`. Its map laws follow by extensionality from
`germSectionsMap_id` and `germSectionsMap_comp`.

`rawCompactGermSectionsFunctor B U` has the same source and target, with
object `AddCommGrpCat.of (CompactGermSections F U)` and map
`compactGermSectionsMap φ U`. It uses the unchanged compact subtype and
the additive structure installed by `CompactGermSections`. Its map laws
similarly use `compactGermSectionsMap_id` and
`compactGermSectionsMap_comp`. The object and map-hom formulas are
definitional equalities. The pointwise map formulas identify the values
with `rawStalkMap φ x.val` applied to the original value at `x : U`,
for both unrestricted and compact sections.

The preceding group-and-map module establishes that these actual maps
preserve compactness: their support is relatively closed in `U` and
contained in the compact source support. Thus the functor preserves
literal compact support; no closure or bounding compact set replaces it.

`rawCompactGermSectionsNatInclusion B U` has these compact and unrestricted
functors as source and target. Its component at `F` is exactly the bundled
`compactGermSectionsInclusionHom F U`. Naturality is a definitional
equality: the compact map is the existing germ map with its compactness
proof attached, and forgetting that proof commutes with the map.
The component-hom, component-function and component-point formulas are
definitional. Each component is injective by
`compactGermSectionsInclusionHom_injective`.

The normalized functors `germSectionsFunctor` and
`compactGermSectionsFunctor` are the composites of the actual
`presheafInclusion B` with the respective raw functors.
`compactGermSectionsNatInclusion` is the raw natural inclusion whiskered
on the left by that same inclusion. The object formulas give exactly
`GermSections F.obj U` and `CompactGermSections F.obj U`; the map-hom
formulas give exactly `germSectionsMap φ.hom U` and
`compactGermSectionsMap φ.hom U`. The compact map's pointwise formula
therefore uses `rawStalkMap φ.hom x.val`. The inclusion's component-hom
and pointwise formulas retain precisely the same underlying section.

The basis-sheaf functors `basisSheafGermSectionsFunctor` and
`basisSheafCompactGermSectionsFunctor` compose these normalized functors
with the actual `sheafForget B`.
`basisSheafCompactGermSectionsNatInclusion` is the normalized natural
inclusion whiskered by `sheafForget B`. Their object formulas expose
`GermSections F.obj.obj U` and `CompactGermSections F.obj.obj U`, and
their map-hom formulas expose the existing maps of `φ.hom.hom`.
The compact map's pointwise formula uses
`rawStalkMap φ.hom.hom x.val`. The inclusion again forgets only the
compactness proof, with its component-hom and pointwise formulas proved
by reflexivity. All normalized and basis-sheaf evaluation formulas follow
definitionally from actual functor composition and whiskering.

The space universe `u` and section universe `v` remain independent.
The topology, basis and open are arbitrary; no separation, local
compactness, sheaf or nonemptiness premise is added to the raw
construction. The normalized and basis-sheaf versions merely restrict
the source category. Empty domains and empty ambient spaces are included
by the same definitions and the underlying group module's empty-case
results.

The domain open is fixed throughout each functor. Original-section
comparison, arbitrary-open compact-support restriction, clopen zero
extension, compact-open exhaustion, scalar structures and exactness are
outside these constructions.
