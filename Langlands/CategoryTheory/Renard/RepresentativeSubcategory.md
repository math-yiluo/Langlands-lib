# Renard A.II.2: a full subcategory of chosen representatives

This pair implements the representative-subcategory construction described at
the start of Renard A.II.2. It constructs actual selected objects, the full
subcategory, its inclusion and objectwise isomorphisms. A proposition about
an actual quasi-inverse and its proof are separate units.

## Source and correspondence

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original A.II.2 introduction, printed pp.250–251 / PDF256–257, was read,
and PDF257 was inspected visually. The paragraph chooses one object from
each isomorphism class and uses all ambient morphisms between these objects.
Its subsequent definition motivates comparison by a quasi-inverse with natural
isomorphisms. No source-specific Renard errata file was found in the current
published or project `notes/errata` locations.

| Lean declaration | Meaning |
| --- | --- |
| `representativeObjects C` | An ambient object is selected precisely when it is the object assigned by `fromSkeleton C` to some isomorphism class. |
| `RepresentativeSubcategory C` | Mathlib's actual `ObjectProperty.FullSubcategory` on that property. |
| `representativeInclusion C` | The full-subcategory inclusion, taking an object to its ambient object and a morphism to its ambient morphism. |
| `representativeOf X` | The selected representative of the isomorphism class of `X`, with its actual membership proof. |
| `representativeIso X` | An actual isomorphism from the included selected representative to `X`. |
| `representative_eq_of_iso` | Isomorphic selected representatives are equal as objects of the full subcategory. |

The object property is the range of a concrete selection function, rather
than an arbitrary predicate supplied as a hypothesis. In particular its
objects are objects of `C`; the category is not merely a quotient type
identified informally with a subcategory. `FullSubcategory` uses all ambient
morphisms, wrapped by `InducedCategory.Hom`. Its identities and compositions
are the ambient ones. The inclusion's full and faithful instances come from
Mathlib's `ObjectProperty.full_ι` and `ObjectProperty.faithful_ι`; they impose
no new hypotheses.

## Construction and intrinsic law

The implementation reuses pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, modules
`CategoryTheory.Skeletal` and
`CategoryTheory.ObjectProperty.FullSubcategory`.
`Skeleton C` is the quotient of ambient objects by existence of an
isomorphism, with Hom types induced on chosen representatives.
`fromSkeleton C` chooses the ambient representative of a class through
`Quotient.out`. `representativeObjects` takes its object range; it does
not duplicate the quotient construction.

`representativeOf X` takes the class `toSkeleton X` and its selected ambient
representative. The range witness is that same class.
`representativeIso X` is Mathlib's `fromSkeletonToSkeletonIso X`, which
chooses an actual isomorphism from the quotient relation. Both object
selection and this isomorphism use classical choice.

For the intrinsic uniqueness law, unpack the two range witnesses. Transport
the given ambient isomorphism along their witness equalities. Its classes
are equal by `congr_toSkeleton_of_iso`, and
`toSkeleton_fromSkeleton_obj` identifies these with the original classes.
Applying the representative selection function gives equality of the
ambient objects. Full-subcategory extensionality then gives equality of
the selected objects. This describes the implemented Lean proof.

## Scope

The ambient category has independent object and Hom universes:
`C : Type u` with `[Category.{v} C]`. The full subcategory has object
universe `u` and Hom universe `v`. The construction requires no
nonemptiness, essential smallness, finiteness or additional categorical
structure. It also applies when `C` is empty. It performs no universe
shrinking.

This pair gives the source construction and short intrinsic law. It does
not construct a reverse functor or prove naturality of quasi-inverse
comparisons; those require their separate statement and exact proof.
The fixed-dimension vector-space example and remaining A.I–A.II assertions
retain their own obligations. No section or whole-book completion is claimed.
