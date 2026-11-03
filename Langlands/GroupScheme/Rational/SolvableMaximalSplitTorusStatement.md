# Conjugacy of maximal split tori in smooth connected solvable groups

`SolvableMaximalSplitTorusConjugacyStatement.{u}` is the solvable case
needed in the proof of the published
`SmoothMaximalSplitTorusConjugacyStatement.{u}`. It quantifies over every
field `k : Type u`, every smooth affine group scheme `G` over `Spec k`
with connected underlying space, and the additional hypothesis
`IsSolvableGroupScheme G`. The latter is the published condition that
the abstract group of points over the algebraic closure is solvable.

For every pair of embeddings `i : T.toGrp ⟶ G` and `i' : T'.toGrp ⟶ G`
that satisfy the published `IsMaximalSplitTorus` predicate, the
conclusion supplies a rational point `g` of `G` and an isomorphism
`e : T.toGrp ≅ T'.toGrp` such that
`i ≫ (G.innerIso g).hom = e.hom ≫ i'`.
The statement retains finite and imperfect fields and all characteristics;
it does not require that `G` itself be split solvable.

This is a derived prerequisite extracted from the proof of
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Theorem C.2.3, printed pp.593–594 (PDF pp.619–620). In its solvable branch,
the source invokes conjugacy of maximal tori in a smooth connected
solvable group and deduces conjugacy of maximal split tori. CGP cites
Borel, *Linear Algebraic Groups*, second edition, §19.2 for that input.
The present declaration records only the split-torus consequence
explicitly asserted by CGP; it does not formalize or prove the stronger
maximal-torus theorem.

Registered source: `conrad-gabber-prasad-2015-pseudo-reductive`,
SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
No project errata file for this source was present when the statement was
prepared. This file defines a proposition, and supplies no proof of it.
