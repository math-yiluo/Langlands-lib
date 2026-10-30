# Renard A.IX: disjoint supports and canonical subobject maps

Authors: Worker 6 and Worker 185. Worker 6 prepared the initial pair;
Worker 185 checked the original passages, current public dependencies and
complete declarations, and prepared the submission. This module states
proposition targets; it proves no orthogonality, intersection or
monomorphism theorem.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.IX, printed page 268 /
PDF page 274. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete implementation page was read as extracted text and visually
checked against the original. It states that for disjoint subsets `S, S'`
of `Irr(M)`, objects `E ∈ M_S` and `E' ∈ M_S'` have zero Hom; it then
states `E_S ∩ E_S' = 0` and the resulting inclusion `E_S ⊕ E_S' ⊂ E`.

The actual simple-subquotient definitions and neighboring A.VI.3 material
on printed263–264/PDF269–270 were read in full for this submission.
The published class and subquotient definitions are now in
`Langlands.CategoryTheory.Renard.CompositionChains`; they are imported
unchanged through `SimpleSupport`. The
supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is a different edition. Its PDF18–19 were read for this submission; the old-page310
letter correction in the supported-sum passage is already incorporated
in the 2026 text. This is a limited comparison and supplies no correction
to the Hom assertion. The public Appendix A correction note concerns
other passages. No dedicated current errata file was found in the known
project errata locations at this check; exhaustive absence is not claimed.

## Parameters and actual objects

The namespace is `Langlands.Renard`. Every target has `C : Type u`,
`[Category.{v} C]`, `[Abelian C]`, and independent source family universe
`w`, ambient Hom universe `v` and ambient object universe `u`. Each
component retains `IsSourceGrothendieck.{w} C → SourceAB6 C` and
quantifies over all `S T : Set (ObjectClass C)` with
`S ⊆ simpleClasses C`, `T ⊆ simpleClasses C` and `Disjoint S T`.
There is no finite-length, size-reduction, well-poweredness, generator,
concrete-category or module hypothesis.

The public `ObjectClass C` is the actual quotient of objects by actual
isomorphism, and `HasSimpleSupport S X` means
`simpleSubquotientClasses X ⊆ S`. The latter includes every actual
simple cokernel of nested subobjects of `X`, including objects of
infinite length. The actual ambient morphisms, subobjects and biproducts
are used throughout. No decomposition certificate is introduced.

## Exact targets

`SimpleSupportHomOrthogonalityStatement C` says that for every actual
`X Y : C` supported on the respective disjoint sets and every actual
`f : X ⟶ Y`, one has `f = 0`. This is the source assertion
`Hom(E,E') = {0}`, expressed using the existing zero morphism. Because
all ordered choices of `S,T,X,Y` are quantified, the target also covers
the opposite direction by swapping them.

`SimpleSupportSubobjectIntersectionStatement C` says that for every
`X : C` and actual `P Q : Subobject X`, support of `(P : C)` on `S`
and `(Q : C)` on `T` implies `P ⊓ Q = ⊥`. The intersection and zero
are those of the actual ambient subobject lattice. The conclusion
asserts zero intersection, without requiring any arbitrary coproduct.

`SimpleSupportSubobjectBiproductMonoStatement C` has the same subobject
hypotheses and says `Mono (biprod.desc P.arrow Q.arrow)`. The map is the
actual canonical morphism from the ambient binary biproduct of `(P : C)`
and `(Q : C)` to `X`, with the actual inclusions as its restrictions.
Binary biproducts exist in the ambient abelian category; no new existence
premise is present. This expresses that the actual sum embeds in `X`.

`SimpleSupportOrthogonalityStatement C` is the conjunction of those
three targets in that order. All four declarations are `def` returning
`Prop`. Each component retains the source assumptions independently;
no desired conclusion is made an antecedent of another target.

## Provenance and remaining obligations

The Hom component is the source assertion. The intersection and monic
canonical-map targets are its internal consequences for arbitrary
supported subobjects of the same object, exposing a reusable version of
the source argument. A later source specialization takes `P = E_S` and
`Q = E_T` only after the separate support theorem for those actual sums
has been proved. Existence of those full indexed sums, the precise
source-size adapters and their support/maximality are separate
obligations. This module does not assert or assume those results.

A proof route uses the actual image factorization of `f`. Epimorphism
and monomorphism transport put every simple subquotient of the image
in both `S` and `T`. Disjointness makes that set empty, and the already
published source zero-detection clause forces the image to be zero.
The intersection component uses its two actual monomorphisms; the
binary-biproduct component follows from zero intersection and the
abelian-category canonical-map criterion. These are suggested proof
routes, with no proof included here.

Source-size arbitrary sum identities, finite Serre/abelian closure,
colimit closure, supported-sum support/maximality, splitting by a subset
or partition and the product-category equivalence retain their separate
tasks and owners. This statement unit closes none of those obligations.
Development compilation and declaration inspection provide no independent
acceptance or publication.
