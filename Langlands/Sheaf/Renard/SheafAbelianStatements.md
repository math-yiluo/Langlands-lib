# Renard A.VI.1: basis-sheaf abelianness at a sufficient section universe

Worker 1153 states two propositions and their source correspondence. Worker 709
contributed the original-source audit, focused specification and sufficient
section-universe design. This is a statement-only unit: neither proposition is
proved here.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.VI.1, printed p.261 / PDF p.267, lists sheaves of abelian groups on a
topological space among the abelian-category examples, then gives axioms
AB0–AB3*. II.2.1, printed pp.33–34 / PDF pp.39–40, defines the chosen-basis
presheaves, their morphisms, the sheaf condition (F) and the category of sheaves.
These three original pages were read and visually checked for this unit.

The separately registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is supplementary errata for the 2010 edition. Its PDF pp.2–3 and 18–19 were
read; these portions do not change the cited basis-sheaf definitions or
abelian-group sheaf example. This is a check of those portions only.

Both definitions are in `Langlands.Sheaf.Renard`. Each is a closed
`Prop`-valued definition, polymorphic in independent universes `u` and `v`,
with the complete term telescope
`∀ (X : Type u) [TopologicalSpace X] (B : OpenBasis X), ...`.
The topology is the supplied one, and `B` is any actual basis of it.

| Proposition | Conclusion for every space, supplied topology and chosen basis |
| --- | --- |
| `BasisSheafAbelianStatement` | `Nonempty (CategoryTheory.Abelian (BasisSheaf.{u,max u v} B))`. |
| `BasisSheafAbelianAxiomsStatement` | `Langlands.Renard.AbelianAxioms (BasisSheaf.{u,max u v} B)`. |

The first proposition packages existence of Mathlib's data-bearing `Abelian`
structure using `Nonempty`. No such structure is an input. The second uses
the existing seven-axiom predicate: existence of a zero object, finite products,
finite coproducts, kernels, cokernels, normal monomorphisms and normal
epimorphisms, with compatible zero-morphism data existentially packaged.
It introduces no new abelian-category predicate.

The published theorem
`Langlands.Renard.abelianAxioms_iff_nonempty_abelian`, applied to
`BasisSheaf.{u,max u v} B` with its existing category instance, identifies these
two conclusions for each `X`, topology and `B`. Therefore the two universally
quantified propositions have the same mathematical meaning. This uses an
existing correspondence between abelian interfaces; it supplies no proof that
the sheaf category satisfies either conclusion.

The imported [BasisPresheaf](BasisPresheaf.md) and [BasisSheaf](BasisSheaf.md)
constructions give the actual category in both targets. A sheaf is a normalized
contravariant functor from the actual inclusion category `BasisOpen B` to
`AddCommGrpCat.{max u v}`, satisfying the published literal `SheafCondition`.
Its original section groups and restriction homomorphisms are retained.
Compatibility compares restrictions on every smaller basis open lying in an
overlap; intersections need not themselves belong to the basis. Morphisms are
the actual natural transformations, as exposed by `sheafHomEquiv`, and the
category instance is the one already supplied by `BasisSheaf`.

The `SheafCondition` encoding uses sets of basis opens. Its published
`SheafCondition.family` theorem and `BasisSheaf.unique_gluing` recover unique
gluing for covering families indexed by any type in any universe. The present
targets impose no bound on cover families and retain all literal covers.
Empty spaces and bases omitting the empty open are included. When an empty
basis open is present, its section group remains trivial and the empty cover
remains part of the sheaf condition. When it is absent, the empty-value
normalization has no basis object to test.

The explicit section-carrier universe `Type (max u v)` is internal
formalization data: it is a sufficient general size chosen for this statement
family, accommodating the space universe `u` as well as the independent
parameter `v`. It is neither a printed hypothesis nor a correction attributed
to Renard. No relation between `u` and `v` is assumed. The declarations make
no unrestricted claim for the original-value category `BasisSheaf.{u,v} B`
and no claim that `max u v` is necessary for each particular space or basis.
The sufficiency proof and every size argument it needs remain later
obligations.

The A.VI.1 example has no total disconnectedness, local compactness,
separation or nonemptiness restriction. The opening II.2.1 definitions also
start with an arbitrary topological space despite the chapter heading. The
propositions preserve that generality and assume no sheafification,
abelianness, source axioms, closure under categorical operations or comparison
with another sheaf category. In particular, neither the raw presheaf category
nor Mathlib's all-open sheaf category replaces the source category.

Exact proofs of both propositions, together with every needed chosen-basis,
all-open or Mathlib comparison and universe argument, remain separate work.
The normalized-presheaf example is also separate. This unit provides the two
statement targets and their source correspondence; it does not close the
sheaf example's proof obligation or A.VI.1.
