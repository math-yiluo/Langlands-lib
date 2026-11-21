# Satake characters and the normalized spherical section

For an ordered tuple of unramified character values, choose the right spherical
vector in the Library's normalized principal series with value the pure tensor
of ones at the identity. Evaluating it at a group element and multiplying the
tensor factors gives the scalar section. It is locally constant by right
invariance under the open spherical subgroup. On the upper Borel, normalized
induction gives the product of the inducing characters times the half modulus.

The standard Hecke operators act on the spherical vectors by their published
Satake scalars. The generation theorem and invertibility of the last standard
operator extend this scalar action to every spherical Hecke function. The
algebraic integrated action evaluated by the scalar functional at the identity
is the Bochner integral of the Hecke function times the section. That product
is integrable by continuity and the compact support of the Hecke function.

This formula connects the Library's `IsSatakeCharacter` to normalized induction
and is an input to the constant-term comparison. Henniart–Lemaire (2011),
I.3.1 gives the Satake and unramified principal-series normalizations. The Lean
proof uses the Library's standard double-coset scalar calculation and
`Hecke.integratedAction_dual`.
