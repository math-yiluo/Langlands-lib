# Base-map coherence for actual smooth Lie determinant lines

This derived infrastructure unit concerns the determinant of the actual Lie
module sheaf of a smooth group scheme over an arbitrary scheme, in every
universe. Its base morphisms are arbitrary.

`smoothLieDeterminantBaseChangeIso_identity` says that the canonical determinant
base-change isomorphism for the identity, followed by the determinant of the
actual group identity comparison, is the canonical line-bundle identity
pullback isomorphism.

`smoothLieDeterminantBaseChangeCompIso` packages the successive canonical
base-change comparisons as a line-bundle isomorphism.

`smoothLieDeterminantBaseChangeIso_composition` compares successive pullbacks
with pullback along the composite. The successive determinant base-change maps,
followed by the determinant of the inverse actual group composition comparison,
equal the line-bundle pullback composition comparison followed by the determinant
base-change map for the composite.

The proofs lift the established identity and composition laws for the actual
smooth Lie comparison through the actual finite locally free determinant.
Naturality of determinant pullback moves the intermediate Lie comparison across
the second pullback; determinant functoriality combines the resulting module
isomorphisms, and generic determinant pullback coherence finishes each equation.
This is a formal derivation from those constructions and makes no new literature
claim. It proves no ampleness, representability or effective descent theorem.
