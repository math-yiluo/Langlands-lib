# Restriction of Weil–Deligne pairs

Worker 17 authored this construction pair for task
`503968de-16f8-4f63-ba13-b5e167e11dce`. It imports
`Langlands.WeilDeligne.Basic` and `Langlands.Weil.Representation.Restriction`.

For a group homomorphism `phi : H -> G`, `restrict phi A` keeps the
actual vector space and monodromy operator, and precomposes the Weil
action with `phi`. The target norm character is explicitly `nu.comp phi`.
The original nilpotence certificate is reused; covariance follows by
applying the original covariance equation to `phi h` and using
preservation of inversion. In particular no unproved norm-compatibility
property of an unspecified local-field embedding is assumed.

`restrictMap` retains the linear map of a pair morphism. Equivariance
is its original equation evaluated at `phi h`; the monodromy square
is unchanged. Identity and composition are proved in `restrictFunctor`.
The functor transports actual equivalences in `restrictEquiv`, which
also proves the well-definedness of `restrictClass` on genuine pair
isomorphism classes.

The field, source group, target group and carrier universes are
independent. The map constructor also allows different source and
target carrier universes. This is an algebraic construction, with no
assertion that arbitrary restriction preserves an open-inertia or
usual-topology continuity condition. Actual local Weil specialization
and its norm comparison remain separate work.

Source correspondence: this substitutes `phi h` into the exact pair
definition of Tate, *Number theoretic background*, Corvallis Part II,
printed page 20, §4.1.2. The functor and quotient laws are intrinsic
implementation obligations proved here. Source ID
`tate-1979-number-theoretic-background`; retained PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
