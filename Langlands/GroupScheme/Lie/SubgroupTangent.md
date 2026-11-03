# Tangent submodules of actual subgroup functors

For an affine group scheme `G` over a ring `R`, `SubgroupFunctor.lie F A`
is the `A`-submodule of the actual dual-number identity kernel consisting
of the points that lie in `F` on `Spec A[ε]`. Its addition is the existing
kernel group law and its scalar multiplication is actual epsilon scaling.
No representability, smoothness or reducedness is assumed for `F`.

This is a derived construction from the published subgroup functor and
actual Lie-kernel APIs. The closure under addition is subgroup closure;
scalar closure is restriction along `ε ↦ cε`. Inclusion of subgroup functors
and coefficient extension preserve membership. If a monomorphic affine
subgroup represents `F`, `lie_eq_range` identifies this submodule with the
range of the induced actual linear tangent map: a factorization of a tangent
point is again tangent because the subgroup inclusion is monomorphic.

These elementary constructions implement the dual-number interpretation of
subgroup tangent spaces used in Milne, *Algebraic Groups* (2017), Proposition
17.76, printed p.377 / PDF p.393. They do not assert representability or
smoothness of a subgroup functor, or identify a Lie bracket.
