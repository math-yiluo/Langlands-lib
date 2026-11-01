# Individual induction–Jacquet terms on quasicuspidal induction

Author: Worker 165.

This is an internal derivation for the segment exchange task. It proves no
signed effectivity or irreducible-image assertion.

`QuasicuspidalInductionTermsStatement` says that, in every positive rank,
for any two block shapes `B` and `C` and any actual finite-length smooth
quasicuspidal representation `A` of the product Levi of `B`, the operator
`i_C r_C` sends the class `i_B[A]` to a natural-number multiple of itself.
No irreducibility or admissibility hypothesis on `A` is imposed.

`inducedGeometricPiece_quasicuspidal` first treats one geometric piece.
The published `normalizedInductionK0_comp_geometricPieceK0` identifies
ambient induction of that piece with `i_B i_S r_S[A]`, where `S` is its
source refinement. A proper source refinement has zero Jacquet class by
quasicuspidality. If the source parabolic is the whole Levi, the published
uniqueness of the whole refinement and its actual induction–Jacquet
equivalence identify this class with `i_B[A]`. This lemma works in every
rank and does not assume minimality of the permutation.

`quasicuspidalInductionTerms` reuses the published
`QuasicuspidalCutSupport.inductionJacquetInduction_natural_multiple` to prove
the unchanged statement. That theorem applies the actual geometric lemma
in positive rank and induces its finite sum of exact classes to the ambient
group. Its multiplier counts the pieces whose source refinement is the
whole refinement, equivalently whose source parabolic is the whole Levi.
The proof neither computes that number nor identifies the induced
representations up to isomorphism.

All classes are those of the existing exact finite-length Grothendieck
groups, retaining every actual short exact sequence relation, including
nonsplit sequences. The supplied prime, p-adic field, and topological data
are arbitrary. Field and carrier universes remain independent, with
carriers in `Type (max uF uV)`. The functors use the existing upper block
parabolics, positive half-modulus covariance, and right translation.

The substantial inputs are the actual geometric-lemma filtration, its
finite-length class formula, induction in stages and whole-Levi invariance
in the induced-piece identity, and vanishing of proper refined Jacquet
modules for quasicuspidal representations. These are independently
established lower algebraic results. This module gives a class identity
for an entire induced object; additional arguments are required to
deduce support preservation for its constituents or positivity of a
virtual Aubert image.
