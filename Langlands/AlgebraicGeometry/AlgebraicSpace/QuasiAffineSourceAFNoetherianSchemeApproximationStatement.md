# Reduction of quasi-affine-source AF representability to Noetherian scheme sources

Author: Worker 1038.

Module
`Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFNoetherianSchemeApproximationStatement`,
namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`. It imports
`Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianSchemeQuasiAffineSourceAFStatement`.

## Statement

`QuasiAffineSourceAFNoetherianSchemeApproximationStatement.{u}` is the implication

`NoetherianSchemeQuasiAffineSourceAFStatement.{u} → FiniteSurjectiveQuasiAffineSourceAFStatement.{u}`.

- The hypothesis is AF representability for a finite surjection from a quasi-affine source
  that is a Noetherian scheme, over every base scheme in universe `u`.
- The conclusion is the published statement over `Spec R`, for every commutative ring
  `R : Type u`, with no Noetherian hypothesis.

## Mathematical content and provenance

Derived. This is the approximation step of Gross, *Tensor generators on schemes and stacks*,
Proposition 3.5 (source `gross-tensor-generators-schemes-stacks-2017`). Step 3 of the proof
(printed p. 511 / PDF p. 11) reads: "By approximating `X` and `p`, we may assume that `X` is of
finite type over `Z`."

The proposition only relates two statements and asserts nothing beyond what the literature's
reduction asserts. It is true by the following argument, which is not part of this
statement:

1. Pass to an absolute presentation of `Y`.
2. Use absolute Noetherian approximation: the Library's published first-level and cover-level
   results, adapted to a cover with quasi-affine quotient, give a Noetherian presentation
   whose finite surjective cover has a quasi-affine quotient. That quotient is open in the
   spectrum of a ring of finite type over `ℤ`, hence a Noetherian scheme.
3. Apply the hypothesis to the corresponding algebraic space.
4. Pull the AF representer back along the cartesian (affine) morphism.
5. Transport the representer and the natural isomorphism to `Spec R`.

This statement supersedes the published `QuasiAffineSourceAFApproximationStatement`, whose
hypothesis assumes only a topologically Noetherian source. The scheme-theoretic hypothesis is
the one that the Noetherian induction for the hypothesis can use directly, and approximation
by finite-type models supplies it.
