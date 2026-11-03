# Geometric structure of a parabolic intersection

Author: Worker 1349.

`Langlands.GroupScheme.ParabolicIntersectionGeometryStatement.{u}` is a
derived structural prerequisite for the common rational maximal torus
theorem. It is stated for every field `k : Type u`, a connected reductive
group scheme `G`, and two actual parabolic subgroup morphisms
`j : P ⟶ G` and `j' : P' ⟶ G`.

Let `H` be their categorical pullback in group schemes and let
`c : H ⟶ G` be its first projection followed by `j`. The proposition
asserts that `H` is smooth over `k`, that its base change to the chosen
algebraic closure of `k` is connected, and that this base change admits a
homomorphism `f` from an actual commutative group scheme `T` whose
composite with the base change of `c` satisfies `IsMaximalTorus` in the
ambient base change of `G`.

In particular, the last clause includes the torus and closed immersion
conditions through the existing `IsMaximalTorus` predicate. Its maximality
is in the ambient group, rather than only in `H`. The map `f` gives
containment on every test scheme. The object `H` is the actual
scheme-theoretic intersection; no reduction or identity component is
substituted. The statement does not require a common torus over `k`,
splitness, perfectness, or a characteristic restriction.

The original geometric inputs are Borel–Tits, *Groupes réductifs*
(1965), Section 2.4, printed page 65 (zero-based PDF page 11), and
Corollary 4.5, printed page 87 (zero-based PDF page 33). Section 2.4
recalls that two Borels over an algebraically closed field have a common
maximal torus, and Corollary 4.5 asserts connectedness of an intersection
of parabolics. These are the geometric full-rank and connectedness inputs
used in the proof of Proposition 4.7, printed page 88 (zero-based PDF
page 34).

Source ID: `borel-tits-1965-groupes-reductifs`; SHA-256:
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
The source's conventions in Section 0.3, printed pages 57–58 (zero-based
PDF pages 3–4), concern absolutely reduced affine algebraic groups.
Consequently, smoothness of the actual categorical pullback is an
additional scheme-theoretic refinement included in this derived
statement, not a verbatim assertion of Corollary 4.5. A proof must establish
that refinement as well as the geometric conclusions. This module
defines the proposition and proves none of its clauses.
