# Proof of initiality of the endomorphism-localization arrows

Authors: Worker 709 wrote the shared proof draft. Worker 1570 checked the source
correspondence and implementation and completed this documentation under task
`348bf102-8242-47f7-b5b2-5ea4429d30da` revision 1.
This file proves the published statement
`Langlands.Renard.EndomorphismLocalization.ChosenComparison.InitialityStatements`
from [`RenardEndomorphismLocalizationInitialityStatements`](RenardEndomorphismLocalizationInitialityStatements.md).
The theorem `initialityStatements` proves it at
independent universes u, v and w with no added hypothesis.

## Source and scope

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1570 reread both pages and checked the fingerprint on 5 November 2026.
The right universal-problem definition on PDF257 gives the factor equation;
example 5 on PDF258 specializes it to linear intertwiners into invertible
pairs. The uniqueness remark on PDF258 gives the comparison principle.
The supplementary 2010-edition author errata, registered as
`renard-2010-corrections-complements`, were checked on PDF18–19; those pages
contain no correction to these passages.

The arbitrary commutative unital ring, full-subcategory formulation, explicit
structured arrows and carrier lifts are internal derived formulations, as
explained in the unchanged statement's Markdown. They are not extra assertions
attributed to Renard. The field clause is the source's setting. The
noncommutative B-module variant remains outside this target.

The proof covers the zero ring, zero modules, and zero or nilpotent
endomorphisms. It adds no nontriviality, dimension, finiteness, size or
injectivity premise. With κ = max u v w, targets are the actual invertible
pairs with carrier in Type κ, and all their linear intertwiners are retained.
The statement and all imported constructions are unchanged.

## Implemented route

Fix a commutative ring R, a pair A with a = `endomorphism R A`, an invertible
pair B with b = `endomorphism R B.obj`, and a morphism g from the raised pair
`(raisedFunctor R).obj A` to `J.obj B`, where J is the invertible-pair inclusion.

- `baseMap g` is the R-linear map `A.a → B.obj.a` obtained by composing the
  underlying map of g with the inverse of `ULift.moduleEquiv`.
  `baseMap_intertwines` is the intertwining equation of g at `ULift.up x`, read
  through `intertwining_iff`.
- `explicitFactor A B g` bundles the published linear factor
  `factor a b B.property (baseMap g) _` from `RenardEndomorphismLocalization`,
  precomposed with `ULift.moduleEquiv`, as a morphism
  `(explicitFunctor R).obj A ⟶ B` of the full subcategory. Its intertwining
  proof is the published `factor_intertwines`.
- `explicitFactor_fac` proves `explicitArrow.app A ≫ J.map (explicitFactor A B g) = g`
  by extensionality on lifted elements and the published `factor_comp_iota`.
- `explicitFactor_unique` shows that every h with the same equation equals
  `explicitFactor A B g`. The underlying linear map of h, precomposed with the
  inverse lift equivalence,
  intertwines `localizedEnd a` with b and composes with `iota a` to `baseMap g`.
  The published `factor_unique` then identifies it with the factor, and
  extensionality of full-subcategory, algebra and module morphisms concludes.

`explicitIsUniversal A` builds initiality data with `IsInitial.ofUniqueHom`:
each structured arrow is sent to `StructuredArrow.homMk` of its factor, and
uniqueness is `explicitFactor_unique` applied to the right component and the
equation `StructuredArrow.w`. `chosenIsUniversal A` transports this along the
inverse of the published `structuredArrowComparison R A` by `IsInitial.ofIso`.

The six clauses then follow:

- both factorization clauses are `StructuredArrow.IsUniversal.existsUnique`
  applied to `StructuredArrow.mk g`;
- both initiality clauses wrap the data in `Nonempty`;
- in comparison uniqueness, the first direction applies `existsUnique` for the
  chosen arrow to the explicit structured arrow, with the published
  `chosenArrow_comparison` as the second witness. The second direction applies
  `existsUnique` for the explicit arrow to the chosen structured arrow, with
  `StructuredArrow.w` of the inverse comparison as the second witness;
- the field clause is the explicit factorization at a field.

`initialityStatements` is the conjunction of these six proved clauses. In
particular, neither initiality proof takes a universal-property certificate as
an input: both provide data for the published structured arrows themselves.
The only axioms are `propext`, `Classical.choice` and `Quot.sound`.
