# Natural finite filtrations of representation functors

Worker 14 implements the actual filtration data needed to state the geometric
lemma without dropping naturality. This pair contains constructions and
predicates, not a proof or an assumption of the geometric lemma.

For a functor `F : C ⥤ Rep R G`, `RepSubfunctor F` assigns a genuine invariant
submodule of every representation `F.obj X`. Its map condition says that the
actual linear map `F.map f` preserves those submodules. `toFunctor` restricts
the original maps. Its identity and composition fields and the naturality and
injectivity of the canonical inclusion are proved.

For subfunctors `S` and `T`, `lowerInUpper` pulls the submodule `S.obj X` back
along the inclusion of `T.obj X`. `quotientObj` is the actual module quotient
of `T.obj X` by that pullback, with the descended representation. Thus it is
`T/(S ∩ T)` in general and the usual `T/S` whenever `S ≤ T`.
`quotientMap` descends the restricted original linear map using `Submodule.mapQ`.
Equivariance is proved on quotient representatives. Identity, composition,
surjectivity of the projection and naturality of the projection are proved.
No quotient object or action law is an unspecified input.

`RepFunctorFiltration F n` consists of `n+1` actual subfunctors, ordered
pointwise, with zero initial submodule and full final submodule.
`graded i` is the quotient of step `i+1` by step `i`, implemented by the
preceding actual quotient construction. Repeated steps and zero pieces are
allowed; strictness and irreducibility would add conditions not present in
the geometric lemma.

`HasGradedPieces` requires natural functor isomorphisms for every graded piece.
`HasOrderedFiltration` existentially quantifies the filtration, while
`IsGluedFrom` additionally allows a permutation of the finite list of pieces.
These are proposition definitions describing data; no existence claim is
made for any induction/Jacquet functor. In particular, there is no field
assuming that an arbitrary representation functor has such a filtration.

The coefficient ring, acting monoid, representation carrier, source-category
objects and source-category morphisms have independent universes. Only a
commutative ring and a monoid are needed. There is no topology or finiteness
condition on a representation carrier. The use of this algebraic framework
for smooth complex representations will be a specialization, with smoothness,
local profiniteness, normalizations and actual parabolic data supplied
separately.

## Original source and scope

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I*, Annales scientifiques de l'ENS (4) 10 (1977), 441–472:

- Section 1.2, printed page 443 (PDF page 4), specifies representations on
  complex vector spaces without a topology on the carrier.
- Sections 1.10–1.11, printed page 445 (PDF page 6), explain subfunctors and
  define gluing by a finite filtration with successive quotients isomorphic
  to the given objects after a permutation.
- Section 2.12, printed page 448 (PDF page 9), requires the filtration and
  graded isomorphisms to depend functorially on the input representation.
- Theorem 5.2, printed page 460 (PDF page 21), gives the ordered version for
  an ordering of double-coset orbits whose initial unions are open.

These original pages were read directly. Literature ID:
`bernstein-zelevinsky-1977-induced-i`; retained PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The broader ring/monoid/category scope is an internal algebraic generalization
of this filtration language, justified by the constructed actions and maps.
It is not an assertion that the source's geometric lemma holds under weaker
hypotheses.

## Dependencies and remaining obligations

This pair uses only pinned Mathlib, chiefly `RepresentationTheory.Rep.Basic`,
`RepresentationTheory.Subrepresentation`, and actual submodule quotients.
It does not recreate the smooth-representation category or its subquotient
interface owned by Worker 23. Those interfaces can supply the source category
or instantiate the resulting functors.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1;
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
There are no project mathematical dependencies.

This pair supplies the filtration language only. The actual geometric-lemma
statement, its parabolic specialization, cuspidal support statements and all
corresponding theorem proofs remain separate obligations. A filtration
interface alone does not complete their assignment.
