# Linearized composition identities of a Cayley datum

Author: Worker 118.

This module derives standard identities of an eight-dimensional unital
composition algebra from the published `CayleyDatum K` interface
(module `Langlands.GroupScheme.Composition.CayleyDatum`): a bilinear
multiplication `μ` on `Fin 8 → K`, a two-sided identity `1`, and a
quadratic norm `N` with `N(1) = 1`, `N(xy) = N(x) N(y)` and nondegenerate
polar form. No characteristic assumption is made; in particular the
identities hold in characteristic two.

## Definitions

- `form` is the polar bilinear form `b(x, y) = N(x + y) - N(x) - N(y)`
  (Mathlib's `QuadraticMap.polarBilin` of the norm). It is an `abbrev`.
- `trace x` is `T(x) = b(x, 1)`.

## Results

Basic facts: `form_apply`, `norm_add` (`N(x + y) = N(x) + N(y) + b(x, y)`),
`form_comm`, `form_self` (`b(x, x) = 2 N(x)`), `trace_unit` (`T(1) = 2`),
additivity and homogeneity of the trace (`trace_add`, `trace_smul`,
`trace_sub`), and the nondegeneracy consequences `eq_of_forall_form_eq`
and `eq_zero_of_forall_form_eq_zero`.

The composition identities, all obtained by linearizing
`N(xy) = N(x) N(y)` and using nondegeneracy of `b`:

- (I1) `form_mul_mul_left`: `b(xy, xz) = N(x) b(y, z)`;
  (I1') `form_mul_mul_right`: `b(yx, zx) = N(x) b(y, z)`.
- (I2) `form_mul_mul_left₂`: `b(xy, wz) + b(wy, xz) = b(x, w) b(y, z)`;
  (I2') `form_mul_mul_right₂`: `b(yx, zw) + b(yw, zx) = b(x, w) b(y, z)`.
- (I3) `form_mul_left`: `b(xy, z) + b(y, xz) = T(x) b(y, z)`, that is
  `b(xy, z) = b(y, x̄z)` with `x̄ = T(x) 1 - x`;
  (I3') `form_mul_right`: `b(yx, z) + b(y, zx) = T(x) b(y, z)`.
- (I4) `mul_mul_left`: `T(x) xz - x(xz) = N(x) z`, that is `x̄(xz) = N(x) z`.
- (I4L) `mul_mul_left₂`:
  `(T(x) yz - x(yz)) + (T(y) xz - y(xz)) = b(x, y) z`, the linearization of (I4).
- (I5) `mul_self`: `x² = T(x) x - N(x) 1`, and its linearization
  `mul_add_mul_comm`: `xy + yx = T(x) y + T(y) x - b(x, y) 1`.
- `mul_mul_self_left`: left alternativity `x(xy) = x² y`.
- `trace_mul`: `T(xy) = T(x) T(y) - b(x, y)`.

## Provenance

These are the standard identities of unital composition algebras, valid
in every characteristic. See Knus, Merkurjev, Rost and Tignol, *The Book
of Involutions*, Section 33.B, the proof of Proposition (33.9), printed
pp.456–458 / PDF pp.479–481. That proof derives (I1), (I1') and the
linearization (33.10) (our (I2)) from `n(xy) = n(x) n(y)`. It then
derives the quadratic equation (33.11) (our (I5)), formula (33.12) (our
(I3)), `x̄(xy) = n(x) y` (our (I4)), alternativity, the linearization
(33.13) (our `mul_add_mul_comm`), and `b(x, y) = T(x) T(y) - T(xy)` (our
`trace_mul`). The Lean proofs
are direct: (I1), (I1') expand `N(x(y + z)) = N(x) N(y + z)` and its
mirror; (I2), (I2') polarize (I1), (I1') in `x`; (I3), (I3') put `w = 1` in
(I2), (I2'); (I4) and (I4L) follow from (I1)–(I3) by testing against an
arbitrary vector and using nondegeneracy of `b`; (I5) is (I4) with `z = 1`;
alternativity follows from (I4) and (I5); `trace_mul` is (I3) with `z = 1`.
The names (I1)–(I5) are labels internal to this development.
