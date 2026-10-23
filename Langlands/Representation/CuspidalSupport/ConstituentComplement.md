# Constituent transfer through complementary invariant subspaces

Authors: Worker 166 (helper proofs) and Worker 67 (closing theorem and packaging).

This module proves the published proposition
`Langlands.CuspidalSupport.ComplementConstituentTransferTheorem.{uR, uG, uV}`
from `Langlands.Representation.CuspidalSupport.ConstituentComplementStatement`.
The closing theorem
`Langlands.CuspidalSupport.complementConstituentTransfer` has exactly that type.
It forms the conjunction of `irreducibleSubquotient_of_isCompl` and
`constituent_of_isCompl`, preserving both universally quantified clauses.

The coefficient, group, and representation-carrier universes `uR`, `uG`,
and `uV` are independent. Both clauses apply to any field `R`, any group `G`
with a topology, actual smooth representations `A` and `D`, and invariant
subspaces `S` and `Q` of `A` whose underlying submodules are complementary.
Complementarity means `IsCompl S.toSubmodule Q.toSubmodule`, so their
intersection is zero and their sum is the whole carrier. There is no
admissibility, finite dimension, finite length, topological group assumption,
or additional theorem-valued hypothesis.

The occurrence and map predicates are the published actual constructions.
`SmoothRep.IsSubquotient D A` means that `D` is isomorphic to a quotient
of an invariant subspace of `A`. `SmoothRep.IsSubrepresentation D A`
and `SmoothRep.IsQuotient D A` assert the existence of an injective
intertwiner `D ⟶ A` and a surjective intertwiner `A ⟶ D`, respectively.

## Implemented proof

The private helper `complementQuotientIso S Q hSQ` identifies the smooth
representation on `Q` with the quotient `A/S`. Its underlying linear
equivalence is the inverse of Mathlib's
`Submodule.quotientEquivOfIsCompl`. This inverse is inclusion of `Q` into
`A` followed by the quotient map. Its intertwining equation is therefore
the one already provided by `SmoothRep.subtype A Q ≫ SmoothRep.mkQ A S`.
`Representation.Equiv.mk` and `SmoothRep.mkIso` package it as an actual
isomorphism of smooth representations.

`irreducibleSubquotient_of_isCompl` assumes that `D` is irreducible, is an
actual subquotient of `A`, and is not an actual subquotient of the
representation on `Q`. The published
`SmoothRep.irreducibleSubquotient_dichotomy` places `D` in the
representation on `S` or in `A/S`. The first alternative is the required
conclusion. In the second alternative, `IsSubquotient.of_iso_right`
transports the occurrence through the inverse of `complementQuotientIso`
to `Q`, contradicting the exclusion hypothesis.

`constituent_of_isCompl` assumes an actual injective intertwiner `i : D ⟶ S`
and an actual surjective intertwiner `q : S ⟶ D`, expressed by the two
published predicates on `SmoothRep.subrepresentation A S`. It constructs:

- the embedding `i ≫ SmoothRep.subtype A S : D ⟶ A`;
- the quotient map `SmoothRep.mkQ A Q ≫ e.inv ≫ q : A ⟶ D`, where
  `e = complementQuotientIso Q S hSQ.symm : S ≅ A/Q`.

The first map is injective by composition with the injective inclusion.
The second is surjective by composition of the quotient map, the
isomorphism inverse, and `q`. This clause does not assume irreducibility.

Finally, `complementConstituentTransfer` applies the conjunction constructor
and supplies these two helper lemmas directly. The helper implementations
and names are preserved from Worker 166's shared constituent draft,
revision 13 of task `fe734e49-26a6-457a-89e8-3b8e66d5cd39`.

## Provenance and scope

This is an internal algebraic result derived from the published
smooth-category subquotient definitions, the proved categorical dichotomy,
and Mathlib's linear algebra of complementary submodules. It imports the
published statement and dichotomy modules and
`Mathlib.LinearAlgebra.Projection`. No published dependency is modified.

The statement's paired Markdown records the motivating use in the
Bernstein–Zelevinsky constituent argument. This proof supplies only the
two stated transfers once complementary invariant subspaces are given.
It does not construct a cuspidal block decomposition or prove the full
Levi constituent theorem.

## Development check

The pair compiled without errors or warnings in the pinned Lean service
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection of the closing
theorem reports the three independent level parameters `uR`, `uG`, and `uV`,
and only `propext`, `Classical.choice`, and `Quot.sound`. Development
compilation is separate from exact-target validation and independent review.
