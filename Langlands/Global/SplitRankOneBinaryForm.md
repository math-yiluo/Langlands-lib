# Binary forms attached to a rank-one lowering curve

Author: Worker 10.

This module is pure linear algebra over a field. It is the first step of the
split rank-one rational-orbit height bound
(`SplitRankOneAdelic.md`). Fix a vector `e` and the polynomial matrices of a
raising map `P` and a lowering map `M` that satisfy the rank-one relation on
`e`. Then the lowering curve `t ↦ M(t) e` has degree at most the coroot weight
`m`. With `w_d` its coefficient vectors, the raising map, the lowering map and
the torus act on the binary form

`ν(X, Y) = ∑_{d ≤ m} X^(m-d) Y^d w_d`

by linear substitutions of `(X, Y)`.

## Provenance

This is internal infrastructure and does not formalize a literature
statement. Springer (*Reduction theory over global fields*, 1994, §3.3)
handles split groups of semisimple rank one through the classification
`H × T` with `H ∈ {GL₂, SL₂, PGL₂}`. The present development avoids that
classification. Instead it records how the rank-one subgroup acts on the
orbit of the highest-weight line, as a binary form of degree `m`. The
facts used are standard `SL₂` representation theory, proved here directly
from the rank-one relation.

## Definitions

- `binaryForm m w X Y = ∑_{d ∈ range (m+1)} (X^(m-d) * Y^d) • w d`, for
  `w : ℕ → n → K`.
- `binaryFormPoly m w p q i`: the `i`-th coordinate with polynomials `p`, `q`
  substituted for `X`, `Y`. `eval_binaryFormPoly` evaluates it.
- `curve M v = M *ᵥ (C ∘ v)`: the polynomial vector `M(X) v`, for a polynomial
  matrix `M : Matrix n n k[X]`.
- `coeffVec M v d`: its coefficient vector of degree `d`.
- `nu m w x = binaryForm m w (x 0) (x 1)`, for `x : Fin 2 → K`.
- `IsBinarySimilitude m w B c`: there are `h : Matrix (Fin 2) (Fin 2) K` and
  `μ : K` with `μ ≠ 0`, `det h ≠ 0`, `μ^2 * (det h)^m = c`, and
  `B *ᵥ nu m w x = μ • nu m w (h *ᵥ x)` for every `x`.

## Results

Generic identities:

- `binaryForm_eval_eq_of_infinite`: two substituted binary forms that agree on
  an infinite set of parameters agree everywhere. The proof compares
  polynomials (`Polynomial.eq_of_infinite_eval_eq`).
- `mulVec_binaryForm` and `smul_binaryForm`: matrices and scalars act on the
  coefficients.
- `binaryForm_eq_pow_smul`: dehomogenization at `X ≠ 0`.
- `binaryForm_one_left`, `binaryForm_zero_one` (`ν(0,1) = w m`), and
  `binaryForm_smul` (`ν(cX, cY) = c^m ν(X, Y)`).
- `mulVec_map_aeval`, `aeval_curve_eq_sum` and `mulVec_map_eval`: evaluate the
  curve, as a finite sum of its coefficient vectors when their degrees are
  bounded.

**Degree bound** (`coeffVec_eq_zero_of_relation`). The field `k` is infinite,
`Mp` and `Mm` are polynomial matrices, and `m : ℤ`. Assume that for every
`t` with `1 + t ≠ 0`,

`Mp(1) (Mm(t) v) = (1 + t)^m • Mm((1+t)⁻¹ t) v`.

Then `coeffVec Mm v d = 0` for every `d > m`. The proof first shows that the top
coefficient `w_D` with `D > m` vanishes. Set `N = D - m ≥ 1`. The polynomial
identity `(1+X)^N · (Mp(1) Mm(X) v)_i = ∑_{d ≤ D} X^d (1+X)^(D-d) w_d i` holds
off `t = -1`, hence everywhere. Evaluating it at `-1` leaves `(-1)^D w_D i = 0`.
A downward induction from a global degree bound then finishes the proof.

Cell actions, over an infinite field `K` and for a curve with
`M t *ᵥ e = binaryForm m w 1 t` for all `t`:

- `binaryForm_eq_curve`: `ν(X, Y) = X^m • M(Y/X) e` for `X ≠ 0`.
- `lowering_mulVec_binaryForm`: if `M` is additive
  (`M (s + t) = M s * M t`), then `M y` sends `ν(X, Y)` to `ν(X, Y + yX)`.
- `raising_mulVec_binaryForm`: assume the relation
  `P s (M t e) = (1+st)^m • M((1+st)⁻¹ t) e` whenever `1 + st ≠ 0`. Then
  `P z` sends `ν(X, Y)` to `ν(X + zY, Y)`.
- `torus_mulVec_binaryForm`: assume `A e = c • e` and
  `A (M t e) = M(a⁻¹ t) (A e)`. Then `A` sends `ν(X, Y)` to `c • ν(X, a⁻¹ Y)`.

Each of these is proved for nonzero `X` (and nonzero `X + zY`) through the
curve, then extended to all `X` by `binaryForm_eval_eq_of_infinite`.

Similitudes:

- `isBinarySimilitude_one` (`B = 1`, `c = 1`).
- `IsBinarySimilitude.mul`: the factors multiply.
- `IsBinarySimilitude.inv`: from a left inverse `B' * B = 1` one gets the
  similitude `c⁻¹`.
- `isBinarySimilitude_lowering` and `isBinarySimilitude_raising`: `c = 1`, with
  `h` the elementary matrices `!![1,0;y,1]` and `!![1,z;0,1]`.
- `isBinarySimilitude_torus`: `c = c_e^2 · (a⁻¹)^m`, where `c_e` is the
  eigenvalue on `e`, with `h = !![1,0;0,a⁻¹]`.
