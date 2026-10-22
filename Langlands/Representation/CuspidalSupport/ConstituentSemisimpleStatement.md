# Semisimple base case for constituent extraction

Authors: Worker 184 and Worker 166.

`Langlands.CuspidalSupport.SemisimpleConstituentExtractionTheorem` is a
Prop-valued definition bundling the following two universally quantified
statements. This file states them without asserting or proving the proposition.
The coefficient, group, and representation-carrier universes `uR`, `uG`, and
`uV` are independent in both clauses.

1. Let `R` be any field, `G` any abstract group, `V` any `R`-module, `ρ` an
   actual representation of `G` on `V`, and `H` any subgroup of `G`. Suppose
   that for every central element `z` there is a scalar `c : R` such that
   `ρ z v = c • v` for every `v : V`. If the restriction of `ρ` to `H` is
   semisimple, its restriction to `H ⊔ Subgroup.center G` is semisimple.
   Semisimplicity is the actual predicate
   `Representation.IsSemisimpleRepresentation`, meaning that every invariant
   subspace has an invariant complement.
2. Let `R` be any field and let `G` have a group structure and a topology.
   For actual smooth representations `A D : SmoothRep R G`, suppose that
   `A.representation` is semisimple and that `SmoothRep.IsSubquotient D A`.
   Then both `SmoothRep.IsSubrepresentation D A` and `SmoothRep.IsQuotient D A`
   hold. These conclusions mean that there is an actual injective intertwiner
   `D ⟶ A` and an actual surjective intertwiner `A ⟶ D`. The subquotient
   hypothesis uses the published relation: `D` is isomorphic to the quotient
   of an actual invariant subspace of `A` by one of its invariant subspaces.

There is no irreducibility, finite-dimensionality, finite-length, or
admissibility hypothesis. The first clause requires neither topology nor
normality of `H`; its scalar condition does not posit a smooth character.
The second clause uses the smoothness already built into `A` and `D`, and
assumes only `[Group G] [TopologicalSpace G]` about the group carrier, with no
continuity axiom on its group operations.

## Internal provenance and scope

These are internal algebraic statements, extracted from the types of Worker
166's draft lemmas `semisimple_sup_center_of_scalar` and
`constituent_of_semisimple`. Their provenance is the existing representation
and smooth-category definitions together with elementary semisimple-module
algebra; the draft proofs are not imported by this statement module.

The first statement is justified algebraically by the identity-on-subspaces
order isomorphism between the `H`-invariant and `H ⊔ center G`-invariant
subspace lattices: stability under scalar multiplication supplies invariance
under the center, and invariant complements transport through this isomorphism.
For the second, the published
`Langlands.SmoothRep.isSubquotient_iff_exists` characterizes a subquotient by
an injection `i : C ⟶ A` and a surjection `q : C ⟶ D`. Over the group algebra,
semisimplicity supplies a retraction `r : A ⟶ C` of `i` and a section
`s : D ⟶ C` of `q`. The composites `i ∘ s` and `q ∘ r` give the requested
injection and surjection. These are descriptions of the algebra underlying
the statements, not proofs supplied by this module.

The motivating application is Bernstein and Zelevinsky, *Representations of
the group GL(n,F) where F is a non-Archimedean local field*, Russian
Mathematical Surveys 31:3 (1976), 1–68, section 3.30(2), printed page 37
(registered source `bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`).
That scalar-center case passes from semisimplicity on `G°` to semisimplicity
on `G° · Z`, then uses a separate finite-index argument to reach `G`, and
finally extracts a constituent as a submodule and a factor module.

The two clauses here isolate the scalar-center and final extraction steps in
greater algebraic generality. They do not include finite-index transfer,
the reduction to a cuspidal summand, or the general central-action argument.
In particular, they do not assert
`Langlands.CuspidalSupport.LeviCuspidalConstituentTheorem`, and they do not
assert that an arbitrary admissible representation is semisimple.
