# Renard A.IX: objects supported on simple isomorphism classes

Authors: Worker 6 and Worker 695. Worker 6 prepared the initial implementation and
companion; Worker 695 checked the original passages, inherited interfaces and
complete declarations, and prepared this submission.

This construction unit defines the full subcategory `M_S` of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, A.IX, printed page 268 / PDF page 274. Its objects are exactly the
objects whose simple subquotient classes all lie in `S`. The module also
collects the actual supported subobjects of an object, for the later
construction of `E_S`.

The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Original PDF pages 269–270 (A.VI.3, `Irr` and `JH`) and 273–275 (including
A.IX) were read. The supported-object definition on PDF274 was also visually
checked against the original page. The public
`Langlands.CategoryTheory.Renard.CompositionChains` pair supplies the actual
constructions used here.

The supplementary 2010-edition errata, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read on PDF pages 18–19. Its old page-310 correction changes `M, M_S` to
`E, E_S` in the later sum construction. The 2026 text already has that
correction; it does not change the supported-object definition. This is a
limited comparison with a different edition, not a claim to have checked all
errata for the book.

## Binders and source correspondence

All declarations are in namespace `Langlands.Renard`. The common binders are
`{C : Type u} [Category.{v} C] [Abelian C]`. The object universe `u` and Hom
universe `v` are independent. No relation between them, finite length,
concreteness, well-poweredness, Grothendieck condition or source AB6 is assumed.

`ObjectClass C : Type u` is the public quotient of actual objects by actual
isomorphism. `simpleClasses C : Set (ObjectClass C)` is the public `Irr(C)`.
`simpleSubquotientClasses X` is the public `JH(X)`: a class `q` belongs to it
exactly when there are actual subobjects `A B : Subobject X` and `h : A ≤ B`
such that `cokernel (Subobject.ofLE A B h)` is simple and its class is `q`.
Thus all simple subquotients are used, even when `X` has infinite length.
This module imports these definitions unchanged.

Renard assumes `S ⊆ Irr(C)` in a Grothendieck category satisfying his source
AB6. Forming `M_S` only requires the displayed support predicate, so the
construction here extends to every abelian category and every set of object
classes. For the source's `S`, it is exactly his full subcategory.
`hasSimpleSupport_inter_simpleClasses_iff` proves that allowing additional
non-simple classes has no effect. No closure or decomposition assertion from
the source is generalized to the weaker setting.

## Definitions

For `S : Set (ObjectClass C)` and `X : C`:

| Declaration | Result | Definition |
| --- | --- | --- |
| `HasSimpleSupport S X` | `Prop` | `simpleSubquotientClasses X ⊆ S` |
| `simpleSupportObjects S` | `ObjectProperty C` | `fun X => HasSimpleSupport S X` |
| `SimpleSupportSubcategory S` | `Type u` | `(simpleSupportObjects S).FullSubcategory` |
| `simpleSupportInclusion S` | `SimpleSupportSubcategory S ⥤ C` | `(simpleSupportObjects S).ι` |
| `simpleSupportSubobjects S X` | `Set (Subobject X)` | `{P | HasSimpleSupport S (P : C)}` |

`HasSimpleSupport` is a predicate, not a theorem target awaiting proof.
The other four declarations are actual mathematical constructions, not
proposition targets. The full subcategory has objects `⟨X, hX⟩`, with
`hX : HasSimpleSupport S X`, and all ambient morphisms between such objects.
Its category and inclusion are Mathlib's actual `ObjectProperty.FullSubcategory`
and `ObjectProperty.ι`. The inclusion is full and faithful by the existing
Mathlib instances. Its object map is `X.obj`, and its morphism map is `f.hom`;
identities and composition are those induced from `C`.

`simpleSupportSubobjects` uses Mathlib's actual subobjects, and tests support
on their underlying objects. It is an indexing set for a later sum. It is not
an object of `C`, a chosen sum, a largest subobject or a maximality certificate.
No cocompleteness assumption or choice of coproduct is needed for this set.
`Subobject X` and its set of supported subobjects live in universe `max u v`;
no well-poweredness or universe reduction is imposed.

## Intrinsic lemmas and their proofs

These short laws explain the constructions; they do not prove any later
source theorem.

- `hasSimpleSupport_iff_subset` and `simpleSupportObjects_apply` are
  definitional unfoldings.
- `hasSimpleSupport_iff` expresses support as
  `∀ (A B : Subobject X) (h : A ≤ B), Simple (cokernel (Subobject.ofLE A B h)) → objectClass (cokernel (Subobject.ofLE A B h)) ∈ S`.
  The forward direction inserts the displayed cokernel into `JH(X)`; the
  reverse direction eliminates a witness of membership in `JH(X)`.
- `simpleSupportInclusion_obj` is definitional equality.
  `hasSimpleSupport_inclusion_obj` is the property field of an actual object
  of the full subcategory.
- `mem_simpleSupportSubobjects_iff` is the defining membership condition.
- `hasSimpleSupport_mono` composes the subset `JH(X) ⊆ S` with `S ⊆ T`.
  `simpleSupportObjects_mono` and `simpleSupportSubobjects_mono` apply this
  same implication pointwise.
- `hasSimpleSupport_inter_iff` proves that support in `S ∩ T` is support in
  both `S` and `T`, by projecting or pairing membership witnesses.
  `simpleSupportSubobjects_inter` applies this to each actual subobject and
  uses set extensionality.
- `hasSimpleSupport_simpleClasses` is the existing public theorem
  `simpleSubquotientClasses_subset_simpleClasses`.
- `hasSimpleSupport_inter_simpleClasses_iff` combines the binary intersection
  law with that existing subset theorem.

## Remaining obligations

This unit supplies the supported-object definition and the indexing set for
supported subobjects. It does not assert or assume isomorphism invariance,
subobject or quotient closure, extension or colimit closure, abelianness of
the full subcategory, the `JH` identities or zero detection. It constructs no
sum `E_S` and proves no support or maximality property of such a sum. Hom
orthogonality, disjointness and direct sums of supported subobjects, splitting
by a subset or partition, subquotient splitting, and the equivalence with a
product of categories remain separate construction, statement and proof
obligations of the whole-book program.


## Development check

The module compiled without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Complete type and body inspection of all
five definitions retained their common binders and independent universes `u, v`.
A separate private probe checked all intrinsic lemma types, unapplied defining
function identities, the inherited category in Hom universe `v`, the existing
full and faithful inclusion instances, and the inclusion's actual morphism map.
These are development checks; independent semantic review and publication are
still required.
