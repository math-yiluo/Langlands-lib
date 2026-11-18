# Statement: compact real-form existence for complex semisimple groups

Author: Worker 263.

`Langlands.GroupScheme.RealCompactFormExistenceStatement : Prop` asserts
that every semisimple group scheme `G` over ℂ is isomorphic over ℂ to the
base change of a semisimple group scheme `H` over ℝ whose full real point
set is compact. This module states the assertion and supplies no proof.
It has no universe parameters.

The witness and the isomorphism are algebraic: `H` is an object of
`GroupScheme (Spec (CommRingCat.of ℝ))`, and the isomorphism belongs to the
category of group schemes over ℂ. `HasCompactRealPoints H` uses the actual
coefficient points with the canonical regular-evaluation topology,
as defined in `Rational.RealCompactPoints`. No representation, positive
definite form, Lie-theoretic compact subgroup or descent datum is supplied
as a premise.

Source: Armand Borel, *Lie Groups and Linear Algebraic Groups, I. Complex
and Real Groups*, retained Hong Kong lecture notes (2000–2001), source ID
`borel-lie-groups-linear-algebraic-groups-2000`. Printed and one-based PDF
pages coincide. Section 5.5, p.39, records compact forms for complex
semisimple Lie algebras and the resulting compact subgroups. Section 5.6,
p.40, states that every connected complex reductive group has a compact
real form. Section 5.7, p.40, discusses the algebraic structure and
complexification of compact forms.

Provenance: derived. We specialize the connected reductive assertion to
semisimple groups and express a compact real form as an actual real group
scheme together with a complexification isomorphism. In characteristic
zero, the smooth affine connected group schemes here are the linear
algebraic groups of the source. The inherited semisimplicity of the form
is included explicitly; its complexification is semisimple. The usual
topology on the real points of an affine algebraic group is encoded by the
canonical topology of regular-function evaluations. The construction of
the real group scheme, its compactness and the algebraic comparison are
all obligations of a future proof.

This assertion is a prerequisite for the real anisotropic-form theorem.
It does not assert uniqueness or the reverse implication from split rank
zero to compact real points.
