# Actual finite-flat pushforward of the structure module

`FiniteFlatPushforwardStructureStatement` concerns the actual scheme-module
pushforward `P = f_* O_X` of a finite flat morphism `f : X → Y`.
It asserts that `P` is quasi-coherent and its sections on every affine open
of `Y` form a finite flat module over the functions on that open.
If `Y` is integral, the rank of that module on any affine open containing
`x` equals the native scheme-morphism rank `f.finrank x`.
The membership hypothesis makes that affine open nonempty.

The assertion is derived from the published affine-local quasi-coherence
closure results, Mathlib's actual localization and tilde equivalence,
`IsFinite.finite_app`, `Flat.flat_appLE`, native rank under pullback,
and `Ideal.finrank_fiber_eq_finrank` on a domain. No Euler-polynomial or
numerical degree assumption occurs. This is geometric preparation for the
native-rank comparison, not the polarized-rank formula itself.
