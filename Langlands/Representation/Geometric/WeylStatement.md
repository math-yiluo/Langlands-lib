# Weyl and Bruhat prerequisites for the p-adic GL geometric lemma

Author: Worker 14. These are proposition definitions over actual matrices,
permutations, subgroups and quotient sets. They assume no theorem truth.
This development depends on the paired `WeylDefinitions` and its explicitly
identified published block and permutation constructions.

`WeylMinimalRepresentativeTheorem` asserts bijectivity of the actual map
from minimal permutations to `W_C \ S_n / W_B`, for positive rank and
arbitrary positive ordered block shapes. Thus both existence and uniqueness
of the representatives are stated, without an arbitrary representative
structure as an input. Minimality means increasing values on each source
block and increasing inverse values on each target block.

`PadicParabolicBruhatTheorem` asserts bijectivity of the map taking the
same actual permutation `w` to the double coset of its inverse permutation
matrix in `P_B \ GL_n(F) / P_C`. The field is any actual `PadicField p`,
for any prime `p` and any positive rank. No extra Bruhat decomposition or
finite double-coset hypothesis is supplied by the caller. Finiteness follows
from the finite permutation subtype if this theorem is later proved.

`PadicStandardIntersectionsTheorem` asserts that each of the two
intersection triples is a standard triple inside its product Levi.
For the source Levi this triple is
`(M intersect w^-1(Q), M intersect w^-1(N), M intersect w^-1(V))`;
for the target it is
`(N intersect w(P), N intersect w(M), N intersect w(U))`.
Each comparison quantifies an actual ordered positive refinement of every
Levi block and equates all three actual subgroups to its product parabolic,
Levi and unipotent radical. The assertion includes the unipotent and
parabolic identifications needed by the later geometric-lemma functors,
rather than merely naming a standard Levi intersection.

`PadicGeometricWeylTheorems` conjoins these three clauses. The field-carrier
universe is arbitrary. No representation-space universe occurs because
these are geometric and combinatorial prerequisites, not representation
classification assertions.

## Original references and specialization

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977):

- Sections 2.1-2.2, printed page 446 (PDF page 7), fix upper standard
  parabolics and identify GL standard Levis with ordered positive blocks.
- Sections 2.6-2.7, printed page 447 (PDF page 8), identify the Weyl action
  on standard Levis. In type A the Weyl group is the permutation group and
  each Levi Weyl subgroup preserves its blocks.
- Lemma 2.11(a), printed page 448 (PDF page 9), gives the unique positive
  representative of each Weyl double coset. Its two positive-root
  conditions are precisely the two within-block inequalities used here.
- Lemma 2.11(b) and section 6.3, printed pages 448 and 468
  (PDF pages 9 and 29), identify both intersection triples as standard.
  Section 6.3 explicitly includes their parabolic and unipotent members.
- Section 6.4, printed pages 468-469 (PDF pages 29-30), uses Bruhat
  decomposition with `w -> w^-1` to identify those representatives with
  `P \ G / Q`, and invokes these triples in geometric lemma 2.12.

All these original passages were read. Literature ID:
`bernstein-zelevinsky-1977-induced-i`. Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The source works with connected reductive groups over nonarchimedean local
fields. The formal specialization fixes the actual `GL_n` matrix group,
upper block parabolics, diagonal torus convention, permutation matrices and
positive roots `e_i-e_j` for `i<j`. Arbitrary finite p-adic extensions are
a subcase of its local fields. Topology choices do not affect these
algebraic subgroup and double-coset assertions, so no topology certificate
is added to the target.

The proof of lemma 2.11(a) in section 6.3 cites Bourbaki's Coxeter-group
exercise; section 6.4 cites Borel--Tits for Bruhat decomposition. These are
proof-source obligations for future proof work; this pair faithfully states
the explicit BZ77 assertions and does not claim to have verified the cited
proofs. No irreducibility or tempered-induction theorem is asserted.

The full normalized parabolic geometric lemma, cancellation of modular
corrections, and the cuspidal-support consequences remain separate targets
to be implemented using these actual constructions and the induction and
Jacquet interfaces maintained by their owners.
