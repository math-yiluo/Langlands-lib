# Analyticity of ordinary common-closure local constants

Worker 1768 states
`Langlands.LocalFactor.CommonClosureSpectralAnalyticStatement.{uF,uV}`.
This is a proposition only. The module proves no analyticity theorem and
constructs no local-constant system.

The proposition quantifies over every prime, p-adic field `F`, reciprocity
family `e`, assignment `ε`, and proof
`hε : NonabelianSystem.IsSystem F e ε`. For every finite intermediate
field `E` in the specified algebraic closure, every supplied nontrivial
continuous unitary additive character `ψ`, every supplied additive Haar
measure `μ`, and every class `x` in the continuous exact virtual group
`Virtual F E`, the complex-valued function

`s ↦ (conditionalDeligneValue F e ε hε E ψ μ x s : ℂ)`

is analytic at every complex point. The field universe `uF` and independent
carrier parameter `uV` retain the published carrier convention
`max uF uV` of `Virtual`. The value is exactly
`ε E ψ μ (virtualTwist F E s x)`, with the original continuous action and
exact quotient. It uses the existing character
`w ↦ exp(-s log(q_F))^(deg_F w)` restricted to the actual subgroup `W_E`.
There is no renormalization of the restricted base degree to degree one
at an extension-field Frobenius.

All intermediate fields use `CommonClosure.fieldData F E`, hence their
canonical local topology and Borel space. The proposition has no
unitarity, irreducibility, finite-inertia presentation, surjectivity,
conductor-formula, self-duality, gamma-comparison, or system-existence
premise beyond the displayed published system and harmonic inputs.
Nonvanishing already follows from the unit-valued codomain of the
supplied assignment; it is not an additional conclusion of this statement.

## Original-source correspondence

The source is John Tate, *Number theoretic background*, Corvallis Part II
(1979), registered as `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
printed p.15, retained PDF p.24.

Tate (3.4.5) gives the stronger formula
`ε(V ω_s, ψ, dx) = ε(V, ψ, dx) f(V)^(-s) δ(ψ)^(-s dim V)`.
Both bases are positive real numbers, so the right side is a constant
times the exponential of a complex linear function of `s`.
It is analytic everywhere. Tate (3.4.2) extends the local constant to
virtual representations by additivity; finite products and inverses
of these nonvanishing exponentials retain this analyticity.
The preceding paragraph on that page obtains the laws for the supplied
system from its rank-one values and degree-zero inductivity. These are
the published relations packaged by `NonabelianSystem.IsSystem`.

This proposition records the derived analytic consequence, rather than
reproducing Tate's numerical conductor formula. The source applies to
each local field. Its use on the actual subgroup `weilSubgroup F E`
still requires the proof to relate the restricted base norm character
to the local field `E`, or to work directly with the common-closure
induction and rank-one relations. No such transport theorem is proved
or assumed in this module. The all-intermediate-field quantifier is
essential: the separate `ConductorExponentStatement` only states
spectral laws at the bottom field of a common closure.

## Consumer and scope

A proof of this proposition supplies the ordinary Deligne analyticity
premise of `CommonClosureGammaAnalytic` at the underlying exact class
of any continuous Weil–Deligne parameter. Its analytic quotient
correction then gives analyticity of the full conditional epsilon.
The present module neither imports that helper nor claims to prove
Henniart's associated-pair induction statement. Arithmetic unitarity,
the self-pair gamma comparison, and the automorphic classification
and induction argument remain separate proof obligations.
