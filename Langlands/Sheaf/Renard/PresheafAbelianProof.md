# Abelianness of normalized basis presheaves

Worker 1595. This pair proves the existing proposition
`Langlands.Sheaf.Renard.PresheafAbelianStatement.{u,v} B` and exposes the
source-axiom corollary
`Langlands.Sheaf.Renard.PresheafAbelianAxiomsStatement.{u,v} B`.
Both targets are imported unchanged from
[PresheafAbelianStatements](PresheafAbelianStatements.md).

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.VI.1, printed p.261 / one-based PDF267, asserts the presheaf example
and states the seven abelian-category axioms. II.2.1, printed p.33 / PDF39,
specifies a chosen basis, trivial sections on its empty open when present,
and natural transformations as morphisms. These two pages were reread
in full and the source fingerprint was verified for this proof.

The supplementary correction list for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread at PDF2–3 and PDF18–19 and its fingerprint verified. Those portions
do not alter the cited definition or example. This bounded check of older
errata does not replace the governing 2026 source.

All declarations below are in `Langlands.Sheaf.Renard`. Their only parameters
are `{X : Type u} [TopologicalSpace X] (B : OpenBasis X)`, with independent
universes `u` and `v`. The existing category is exactly
the full subcategory of
`RawPresheaf.{u,v} B = (BasisOpen B)ᵒᵖ ⥤ AddCommGrpCat.{v}`
defined by `IsNormalized`. The section groups and restriction maps are the
original values and maps of those functors; the existing full-subcategory
morphisms carry their actual natural transformations.

The implemented proof uses the abelianness of `AddCommGrpCat` and Mathlib's
abelianness construction for functor categories. It then proves the required
closure properties of the actual normalization predicate:

- `isNormalized_containsZero` evaluates the ambient zero presheaf at each
  empty basis open. Evaluation preserves zero morphisms and sends a zero
  object to a zero object. A zero abelian group has a subsingleton carrier.
- `isNormalized_isClosedUnderSubobjects` takes a monomorphism into a
  normalized presheaf. Its components are monomorphisms because evaluation
  into a category with pullbacks preserves them. At an empty basis open,
  the target is a zero group. `IsZero.of_mono` makes the source a zero group,
  hence its carrier is subsingleton.
- `isNormalized_isClosedUnderQuotients` uses the dual argument. Components
  of an epimorphism are epimorphisms, using pushouts in the group category.
  At an empty basis open, `IsZero.of_epi` makes the target of such a
  component a zero group when its source is zero.
- `isNormalized_isClosedUnderFiniteProducts` evaluates a limiting cone
  for a finite discrete diagram. Evaluation preserves this limit. Each
  evaluated diagram object is a zero group at an empty basis open, so
  `Functor.isZero_iff` identifies the evaluated diagram as a zero functor.
  `IsLimit.isZero_pt` makes its limit point a zero group. This argument
  includes the empty product.

Mathlib derives kernel closure from subobject closure and cokernel closure
from quotient closure. Its theorem in
`Mathlib.CategoryTheory.Abelian.Subcategory` then constructs abelian data
on the same full subcategory from zero containment, kernel and cokernel
closure, and finite-product closure. `presheafAbelian` exposes the resulting
`Abelian (Presheaf.{u,v} B)` instance. In particular, the implementation
supplies the finite-product and zero conditions as well as the two closure
conditions; the source's separate insufficient full-subcategory criterion
is not used.

`presheafAbelianStatement` packages this constructed structure in `Nonempty`
and has exactly the published target
`PresheafAbelianStatement.{u,v} B`.
`presheafAbelianAxiomsStatement` applies
`Langlands.Renard.abelianAxioms_iff_nonempty_abelian`
to obtain exactly `PresheafAbelianAxiomsStatement.{u,v} B`, using the
existing seven-axiom interface without introducing a second one.
The closure lemmas and the Mathlib construction route are internal
derived proofs of the cited example, rather than a proof printed on the
source page.

All component groups retain carriers in `Type v`. The proof needs only
finite categorical constructions, so it introduces no comparison between
`u` and `v`. It uses neither points of the space nor an empty basis object
as a witness: every normalization argument is conditional on an existing
basis open being empty. Thus empty spaces and bases omitting the empty
open are included. No abelianness, normalization closure, category
equivalence, sheafification, or extra topological condition is assumed.
Sheaf abelianness, chosen-basis/all-open comparisons, and the star-sheaf
size obstruction retain their separate statements and proofs.
