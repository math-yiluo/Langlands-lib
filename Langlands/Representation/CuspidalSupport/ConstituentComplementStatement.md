# Constituent transfer through complementary invariant subspaces

Authors: Worker 283 and Worker 166.

`Langlands.CuspidalSupport.ComplementConstituentTransferTheorem` is a
Prop-valued definition bundling the following two universally quantified
statements. This file states them without asserting or proving the proposition.
In both clauses `R` is any field, `G` is any type with a group structure and a
topology, `A D : SmoothRep R G` are actual smooth representations, and
`S Q : Subrepresentation A.representation` are actual invariant subspaces of
`A` whose underlying submodules satisfy
`IsCompl S.toSubmodule Q.toSubmodule`. This is Mathlib's lattice
complementarity: `S ⊓ Q = ⊥` and `S ⊔ Q = ⊤` as submodules, so the carrier of
`A` is the internal direct sum of the two subspaces. The coefficient, group,
and representation-carrier universes `uR`, `uG`, and `uV` are independent.

1. Suppose that `D` is irreducible (`SmoothRep.IsIrreducible`, Mathlib's
   simplicity of the invariant-submodule lattice, which includes
   nonzeroness), that `SmoothRep.IsSubquotient D A`, and that `D` is not a
   `SmoothRep.IsSubquotient` of `SmoothRep.subrepresentation A Q`. Then `D` is
   a `SmoothRep.IsSubquotient` of `SmoothRep.subrepresentation A S`.
2. Suppose that `D` satisfies both
   `SmoothRep.IsSubrepresentation D (SmoothRep.subrepresentation A S)` and
   `SmoothRep.IsQuotient D (SmoothRep.subrepresentation A S)`. Then both
   `SmoothRep.IsSubrepresentation D A` and `SmoothRep.IsQuotient D A` hold.
   This clause has no irreducibility hypothesis.

The predicates are the published ones. `SmoothRep.subrepresentation A S` is
the smooth representation on the actual invariant submodule `S`.
`SmoothRep.IsSubrepresentation B C` means that there is an actual injective
intertwiner `B ⟶ C`, and `SmoothRep.IsQuotient B C` means that there is an
actual surjective intertwiner `C ⟶ B`. `SmoothRep.IsSubquotient B C` means
that `B` is isomorphic to the quotient of an actual invariant subspace of `C`
by one of its invariant subspaces.

There is no finite-dimensionality, admissibility, or finite-length
hypothesis. About the group carrier the statement assumes only
`[Group G] [TopologicalSpace G]`, with no continuity, local compactness, or
other topological axiom. Smoothness enters only through the structure already
carried by `A` and `D`.

## Internal provenance and scope

These are internal algebraic statements. Their exact types are those of Worker
166's draft lemmas `irreducibleSubquotient_of_isCompl` and
`constituent_of_isCompl` (shared draft of task
`fe734e49-26a6-457a-89e8-3b8e66d5cd39`, revision 7, file
`Langlands/Representation/CuspidalSupport/ConstituentComplement.lean`),
written here as two universally quantified conjuncts. This statement module
imports only the published smooth-category subquotient definitions; it does
not import the draft proofs.

Their provenance is the published smooth-category definitions, the published
irreducible-subquotient dichotomy
`Langlands.SmoothRep.IrreducibleSubquotientDichotomy`, and elementary linear
algebra of complementary submodules in Mathlib. When `S` and `Q` are
complementary, inclusion of `Q` followed by the quotient map identifies `Q`
with the quotient `A/S` as representations. Mathlib's
`Submodule.quotientEquivOfIsCompl` supplies the linear isomorphism. For the
first clause, the dichotomy places an irreducible subquotient of `A` in `S` or
in `A/S`, and the identification `A/S ≅ Q` rules out the second alternative.
For the second clause, an embedding into `S` composes with the inclusion
`S ⟶ A`. A quotient map from `S` composes with `A ⟶ A/Q ≅ S`. These are
descriptions of the algebra underlying the statements, not proofs supplied by
this module.

The motivating application is Bernstein and Zelevinsky, *Representations of
the group GL(n,F) where F is a non-Archimedean local field*, Russian
Mathematical Surveys 31:3 (1976), 1–68 (registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`). The
proposition in section 3.28, printed page 36, splits a representation `E` as
`E = E₁ ⊕ E₂` of submodules, where `E₁` is quasi-cuspidal and all of its
irreducible subfactor modules have the form `ψω` for an irreducible cuspidal
`ω` and a character `ψ` trivial on `G°`, and no irreducible subfactor module
of `E₂` has that form. Step (1) of the proof
of Proposition 3.30, printed page 37, then reduces constituent extraction to
the summand `E₁`. The two clauses here are the algebra behind that reduction:
the first moves an irreducible subquotient into the summand that can contain
it, and the second returns a submodule and factor module found in the summand
to the whole representation.

The statements are broader than that application and contain none of its
specific content. They do not assert the existence of the section 3.28
decomposition, any property of cuspidal or quasi-cuspidal representations,
the semisimple extraction step, or
`Langlands.CuspidalSupport.LeviCuspidalConstituentTheorem`.
