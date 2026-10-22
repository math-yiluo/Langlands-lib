# Bundled smooth representations

This development packages the accepted smoothness predicate as the full
subcategory `Langlands.SmoothRep R G` of Mathlib's `Rep R G`. Its objects have
actual algebraic actions, and its morphisms are exactly equivariant linear maps.
The category and its additive and linear structures are inherited from Mathlib.
`of`, `ofHom`, `toRep`, `mkIso` and `equivOfIso` provide the explicit interfaces.
The elementary morphism laws follow by the definitions.

## Canonical name and induction compatibility

This is the canonical category also used by the induction constructions.
[`Representation/Induction/Definitions`](../Induction/Definitions.md) imports
this module and retains `Langlands.Induction.SmoothRep` as a transparent
compatibility abbreviation:

| Retained name | Canonical name |
| --- | --- |
| `Langlands.Induction.SmoothRep.{uR,uG,uV} R G` | `Langlands.SmoothRep.{uR,uG,uV} R G` |
| `Langlands.Representation.Category.Basic` | Unchanged module path |
| `Langlands.Representation.Induction.Definitions` | Unchanged module path importing this category |

The alias has the same explicit `R G` arguments, three independent universes,
and `CommRing R`, `Group G`, `TopologicalSpace G` instance telescope.
Unfolding `smoothRepProperty` identifies it definitionally with induction's
former full-subcategory expression. The existing category, additive and linear
instances are reused. There is no intervening category equivalence.
The direct checks in
[`Induction/CategoryCompatibility`](../Induction/CategoryCompatibility.md)
also cover the four induction functors and their maps. Worker 23 authored the
canonical category; Worker 15 authored the induction compatibility
consolidation and these documentation updates. The canonical Lean source is
unchanged by that consolidation.

## Scope

The coefficient ring is commutative; the group has a topology. No continuity of
group operations is needed merely to form this category using the accepted
open-subgroup definition. No topology or finite-dimensionality is imposed on
the representation carrier. The irreducible smooth dual specializes the
coefficient ring to a field.

`HasFiniteLength` means finite composition length as a module over the group
algebra `R[G]`. It does not mean finite length over `R`, which would incorrectly
exclude many infinite-dimensional smooth representations. `HasCentralCharacter`
asserts that a specified character of the actual center acts by its scalar
values. This predicate does not assert that any such character exists or is
unique. `IsAdmissible` retains the accepted quantification over every open
subgroup. `IsIrreducible` reuses Mathlib's simple invariant-submodule lattice,
including its nontriviality condition.

`IsoClass` is the actual quotient by categorical isomorphism. The proved
`isoClass_eq_iff` identifies its equality with existence of an isomorphism.
`SmoothDualClass` is the same quotient construction on the full subcategory of
irreducible admissible objects. Both keep the carrier universe fixed explicitly;
their ambient object universe includes its successor. This file asserts neither
smallness of all representation classes nor a canonical representative.
The name distinguishes this space of isomorphism classes from the existing
`Langlands.SmoothDual ρ`, which is the vector space of smooth linear functionals.

## Sources and correspondence

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), section 1.2, printed page 443 (PDF page 4), defines smooth representations,
their intertwiner category, isomorphism classes of irreducibles, subquotients and
finite length. Section 1.3 on the same page gives admissibility; section 1.5
discusses scalar characters. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original passage was read directly. Its complex, locally profinite setting
is retained as a specialization. The broader ring/topology scope here is a
derived domain of definition only, with no source theorem asserted at that scope.
The center predicate is an explicit algebraic specification of scalar action,
not a claimed central-character existence theorem from that passage.

The group-algebra formulation of finite length uses the equivalence between
invariant submodules and group-algebra submodules implemented by Mathlib
`Subrepresentation.asSubmodule`. The universe-indexed quotient is a formal
implementation choice that avoids an unproved smallness claim.

## Dependencies

The accepted smoothness predicate is `Langlands.IsSmooth`, imported from
`Langlands.Representation.Smooth.Definitions`. The canonical category's Lean
source is unchanged at the compatibility consolidation's Library base
`30ceb5a0d89d8094c1663fc19f35416519b9a125`.

The pinned environment is artifact
`2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1: Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Audited interfaces are
`RepresentationTheory/Rep/Basic.lean`, `RepresentationTheory/Irreducible.lean`,
`RepresentationTheory/Subrepresentation.lean`,
`CategoryTheory/ObjectProperty/FullSubcategory.lean`,
`CategoryTheory/Skeletal.lean` and `RingTheory/FiniteLength.lean`.

This is a construction layer. Abelian-category closure, classification,
supercuspidality, central-character existence and Langlands quotient existence
are not supplied by this file.
