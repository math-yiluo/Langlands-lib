# Automorphisms of the split Cayley algebra preserve its norm

Author: Worker 161.

This module shows that, over a field, every unit-fixing linear automorphism
of the Zorn product preserves the Zorn norm. In particular this holds for
every automorphism matrix of `CayleyDatum.split K` with coefficients in a
field. The result holds in every characteristic. A Galois-descent argument
in `CayleyGaloisTwist` uses it to descend the norm of a twisted Cayley
datum. The module also records that automorphism matrices of any Cayley
datum are stable under change of coefficients.

## Declarations

- `SplitCayley.trace R x` is `x₀ + x₇`, the trace `a + b` of the Zorn vector
  matrix `(a, u, v, b)`.
- `SplitCayley.mul_self`: over every commutative ring,
  `x x = T(x) x - N(x) 1`. Here `T` is the trace, `N` the Zorn norm and `1`
  the vector `(1, 0, 0, 1)`. This is a coordinatewise polynomial identity,
  checked by `simp` and `ring`.
- `SplitCayley.norm_mulVec_eq`: let `F` be a field and `g ∈ GL₈(F)` fix `1`
  and satisfy `g(xy) = (gx)(gy)` for all `x, y`. Then `N(gx) = N(x)`. Put
  `y = gx`. Applying `g` to the quadratic equation of `x` gives
  `y y = T(x) y - N(x) 1`. The quadratic equation of `y` gives
  `y y = T(y) y - N(y) 1`. Hence `(T(x) - T(y)) y = (N(x) - N(y)) 1`.
  - If `T(x) = T(y)`, comparing coordinate `0` gives `N(x) = N(y)`.
  - Otherwise `y = c 1` for a scalar `c`. Since `g⁻¹` also fixes `1`,
    `x = g⁻¹ y = c 1 = y`, so `T(x) = T(y)`, a contradiction.

  Only division by the nonzero scalar `T(x) - T(y)` occurs, so no
  restriction on the characteristic is needed.
- `SplitCayley.polar_norm_mulVec_eq`: the polar form of the norm is
  preserved as well. It is expressed through the norm, and `g` is
  additive.
- `CayleyDatum.split_norm_mulVec_eq`: for a ring homomorphism `φ : K →+* F`
  into a field, every `g` with `(split K).IsAutomorphismMatrix φ g`
  preserves `SplitCayley.norm F`. The published `split_unitOver` and
  `split_multiplicationOver` turn the automorphism equations into the two
  hypotheses of `norm_mulVec_eq`.
- `CayleyDatum.IsAutomorphismMatrix.map`: for every Cayley datum `c` and
  ring homomorphisms `φ : K →+* A`, `f : A →+* B`, if `g` is an automorphism
  matrix of `c` along `φ`, then `g` with `f` applied to its entries is one
  along `f ∘ φ`. The proof uses `isAutomorphismMatrix_iff` with
  `map_unitDefect` and `map_multiplicationDefect` from
  `CayleyAutomorphismGroup`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
Proposition 33.27(2), printed p.462 / PDF p.485. It states that every
isomorphism of composition algebras is an isometry of their norms, even
without an identity element. This module proves the special case of
automorphisms of the split Cayley algebra over a field, with its own
elementary argument through the quadratic equation; the source proof is
not followed.
