# The anisotropic quadratic dimension bound over nonarchimedean local fields

`Langlands.LocalQuadraticAnisotropicDimensionBoundStatement.{u,v}` asserts
that every anisotropic `QuadraticForm K V` over a nonarchimedean local field
`K` has `Module.finrank K V ≤ 4`. The field and finite-dimensional vector
space have independent universes. All field and residue characteristics
are included. No nonsingularity or condition on the polar radical is assumed.
This file states the proposition and supplies no proof.

The predicate `QuadraticMap.Anisotropic` means that `Q x = 0` forces `x = 0`.
Mathlib's `IsNonarchimedeanLocalField` gives a compatible nontrivial discrete
valuation, finite residue field, and completeness for the compatible additive
uniformity. These are the local-field conditions needed for the source
specialization below.

The statement is derived from Holger P. Petersson, *Anisotropic quadratic
forms over local fields* (March 26, 2013), registered
`petersson-2013-anisotropic-quadratic-local`. Sections 1.1–1.2, pp.1–2, use
the same quadratic and anisotropy conventions, including singular forms in
characteristic two. Sections 2.1–2.4, pp.2–4, construct two anisotropic
residue quadratic forms over the residue field of a complete discretely
valued field. Section 2.5(a), p.4, formula (13), expresses the original
dimension as the sum of their dimensions. Over a finite field each residue
dimension is at most two: Chevalley–Warning applied to a quadratic polynomial
in more than two variables gives a nonzero zero. Thus the sum is at most
four. This finite-field argument applies in characteristic two as well;
it is not an inference that every anisotropic form is nonsingular.

The original residue-form theorem is more general than this finite-residue-field
specialization. The asserted dimension bound still needs a Lean proof,
including the residue-form construction or another valid arithmetic argument.
Mathlib's `char_dvd_card_solutions` is a possible input to its
finite-field step.

This is a generic arithmetic prerequisite for local form classification.
For a Hermitian form over a separable quadratic extension, an actual
base-field quadratic form with the same zero vectors and twice the dimension
turns this bound into a Hermitian dimension bound. That application requires
the separate comparison proof and does not by itself classify group schemes.
