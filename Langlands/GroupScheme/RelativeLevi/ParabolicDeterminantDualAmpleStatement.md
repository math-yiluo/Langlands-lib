# Ampleness of the actual parabolic Lie determinant dual

`Langlands.GroupScheme.FiniteAffineParabolicDeterminantDualAmpleStatement.{u}`
asserts the following local positivity result. Let `R : Type u` be any
commutative ring, let `G` be a reductive group scheme over `Spec R`, and let
`j a : P a ⟶ G` be a family of actual relative parabolic subgroups indexed
by an arbitrary finite type `I : Type u`. Form the actual smooth proper
scheme `finiteAffineParabolicQuotient hG j hj`, the finite coproduct of the
quotients `G / P a`. On this scheme,
`finiteAffineParabolicFamily hG j hj` is the actual parabolic family obtained
by gluing the universal conjugate parabolic families of the components.

The statement says that the dual of the Lie determinant of its chosen
`parabolicRepresentative` is ample. Here `lieDeterminant` is the determinant
line of the actual Lie sheaf of the representative group, and `dual` is its
actual internal module dual, packaged as a line bundle. `LineBundle.IsAmple`
requires quasi-compactness and affine generation loci of global sections of
positive tensor powers covering the scheme.

The source is Brian Conrad, *Reductive group schemes* (2014), Theorem 2.3.6(2),
pp.72–75, and its application in the proof of Corollary 5.2.9, p.157
(registered source `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
Theorem 2.3.6 supplies relative ampleness of precisely the dual determinant
of the Lie sheaf of the universal conjugate subgroup on each quotient. Its
remark on p.72 identifies fibrewise ampleness with ampleness over affine
opens for these proper finitely presented quotients. Page 157 applies this
polarization to a finite coproduct of parabolic quotients. The present
formulation isolates that finite coproduct positivity consequence for the
already constructed actual quotient families; it does not require them to
represent all parabolics.

There is no noetherian, splitting, constant-rank, nonempty-index,
pairwise-distinct-type or completeness hypothesis. The use of a chosen
representative does not alter the mathematical line-bundle isomorphism class:
the inclusion-compatible representative comparisons induce the existing
Lie determinant isomorphisms.

This module defines a proposition and gives no proof of it. In particular,
neither determinant-dual ampleness nor the host smooth proper representability
statement is established here. A proof must supply geometric positivity for
this actual line bundle; existence of a possibly different ample bundle on
the quotient does not suffice.
