# An uncertainty principle for the two block rotations of `O(3)`

Lean module: `Langlands.Representation.Archimedean.RealOrthogonalUncertaintyStatement`
(namespace `Langlands.Archimedean`).

Worker 763 wrote this module for Task 7133 (`534c17c3-0cef-4982-b771-0750d513e885`), the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement` (module
`RealInducedPairFiltrationReduction`). It states one proposition and proves nothing. The
proposition is a fact about functions on the compact group `O(3)` alone; see "Use" below for
where the `GL₃(ℝ)` argument needs it.

## Notation

These are the Library's definitions (module `StandardModule`); nothing new is defined here.

* `GL_3(ℝ)` is `Langlands.GeneralLinear 3 ℝ` and `O(3)` is its subgroup `unitaryCompact ℝ 3`.
* `r_p(θ) = blockRotation 3 p θ = exp(θ (E_{p+1,p} - E_{p,p+1}))`. The Library module
  `RealBlockRotation` proves (`blockRotation_val_eq`, `blockRotation_apply`) that for `p + 1 < 3`
  this is the rotation by `θ` in the coordinates `p, p + 1`, with block
  `[[cos θ, -sin θ], [sin θ, cos θ]]` there and the identity elsewhere. So `r_0(θ)` is the rotation
  about the coordinate axis `e_2` and `r_1(θ)` the rotation about the coordinate axis `e_0`; the
  two axes are orthogonal.
* For `f : GL_3(ℝ) → ℂ`, `p : ℕ`, `j : ℤ` and `g ∈ GL_3(ℝ)`,
  `blockFourierCoefficient 3 p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ` (interval integral). It
  is the `j`-th Fourier coefficient of `θ ↦ f(r_p(θ) g)`, the left Fourier mode `j` of `f` along
  `r_p` at `g`.
* "Right `O(3)`-finite" is `f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (GL_3(ℝ)))
  (unitaryCompact ℝ 3)`: the right translates `g ↦ f(g k)`, `k ∈ O(3)`, span a
  finite-dimensional space of functions on `GL_3(ℝ)`.

## The statement

`RealOrthogonalBlockUncertaintyStatement`: for all natural numbers `p, q, n, n'` and every
`f : GL_3(ℝ) → ℂ` such that

1. `(p, q) = (0, 1)` or `(p, q) = (1, 0)`;
2. `n' < n`;
3. `f` is continuous;
4. `f` is right `O(3)`-finite;
5. for every `g ∈ O(3)` and every integer `j` with `|j| < n`,
   `blockFourierCoefficient 3 p j f g = 0` (all left modes of `f` along `r_p` on `O(3)` are at
   least `n` in absolute value);
6. for every `g ∈ O(3)` and every integer `j` with `n' ≤ |j|`,
   `blockFourierCoefficient 3 q j f g = 0` (all left modes of `f` along `r_q` on `O(3)` are
   smaller than `n'` in absolute value);

we have `f g = 0` for every `g ∈ O(3)`.

No parity of the modes is assumed, and nothing is said about `f` off `O(3)`. Hypotheses 5 and 6
only concern points of `O(3)`, where `r_p(θ) g` and `r_q(θ) g` stay in `O(3)`.

Edge cases. For `n' = 0`, hypothesis 6 says that all modes along `r_q` vanish, and the
conclusion is the Library's `RealBlockFourierFinite.eq_zero_of_blockFourierCoefficient_eq_zero`.
The hypothesis `n' < n` cannot be weakened to `n' ≤ n`: for `(p, q) = (0, 1)` and `n = n' = 1`,
the entry `f(g) = g_{0,2}` is continuous and right `O(3)`-finite, `f(r_0(θ) g) =
cos θ g_{0,2} - sin θ g_{1,2}` has only the modes `±1`, and `f(r_1(θ) g) = g_{0,2}` has only the
mode `0`; but `f` does not vanish on `O(3)` (it is `1` at the permutation matrix exchanging the
coordinates `0` and `2`).

## Why the statement holds

This section explains why the proposition is true; none of it is proved in Lean.

**`K`-types.** The restriction of a continuous right `O(3)`-finite function to `SO(3)` is a
finite sum of matrix coefficients `g ↦ ⟨τ(g) u, v⟩` of irreducible representations `τ` (and
`O(3) = SO(3) × {±1}`, so the same holds on the other component). Hypotheses 5 and 6 are
conditions on the vectors `u` under the rotations `r_p` and `r_q`, so it suffices to show that a
vector `u` of an irreducible representation whose weights for the rotations about one axis are
at least `n` in absolute value, and whose weights for the rotations about an orthogonal axis are
smaller than `n'`, is zero. Realize the representation of degree `L` by the harmonic homogeneous
polynomials `P` of degree `L` on `ℝ³`, with the axis of `r_p` the `z`-axis and the axis of
`r_q` the `x`-axis. The first condition says that `P` vanishes to order `n` along the `z`-axis.
The second says that `P` restricted to every circle about the `x`-axis is a trigonometric
polynomial of degree at most `n' - 1`. On the great circle of the plane `x = 0`, which passes
through the two points `(0, 0, ±1)` of the `z`-axis, `P` is therefore a trigonometric polynomial
of degree at most `n' - 1` with two zeros of order `n`, so it vanishes there (`2n > 2n' - 2`).
The derivative `∂P/∂x` satisfies the same conditions with `n - 1` in place of `n`, and
`n - 1 ≥ n'`, so it also vanishes on the plane `x = 0`. A harmonic polynomial that vanishes with
its normal derivative on a plane is `0`.

**A route through `sl₂`.** A proof that avoids the classification of the irreducible
representations: (1) by left translation with `r_p(π)` and `r_q(π)`, which conjugate `r_q` and
`r_p` into their inverses, one may assume that the modes along `r_p` and along `r_q` have fixed
parities; (2) the restriction of `f` to `O(3)` is a polynomial in the matrix entries
(`OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`), and the polynomial
functions of bounded degree on `O(3)` form a finite-dimensional space stable under the left
derivatives along `𝔰𝔬(3)`; (3) for the generator `L_p` of the left rotations `r_p`, the
complexified generators of the other two rotations give ladder operators `E_±` that raise and
lower the modes along `r_p` by one, with `[E_+, E_-]` a multiple of `L_p` and the generator of
`r_q` equal to `(E_+ + E_-)/2`; (4) the modes along `r_q` lie in a set of at most `n'` values, so
a polynomial of degree `d ≤ n' < n` in the generator of `r_q` kills `f`; (5) the component of
this identity in the mode `k - d`, where `k ≥ n` is the smallest positive mode of `f` along
`r_p`, is `E_-^d f_k = 0` for the mode-`k` component `f_k`, since `k - d > 0` and the negative
modes `≤ -n` cannot be raised to `k - d` by `d` steps. In a finite-dimensional representation of
`sl₂` a lowest-weight vector has weight `≤ 0`, so `f_k = 0`; symmetrically for the negative modes.

## Use

In the proof of `RealCharacterInducedFiltrationStatement`, the standard module of a character
`χ = sgn^ε |·|^s` followed by an induction block `D` of weight `ℓ` and exponent `t` has to be
reached from the standard module of `[D, χ]` by a composite of block Fourier multiplier maps
(module `RealBlockMultiplier`). When `t - s - ℓ/2 = -m` for an integer `1 ≤ m < ℓ/2`, one of the
two multipliers is a tail multiplier whose kernel consists of the functions whose modes along
`r_1` are smaller than `m`, while the `O(3)`-finite functions of the standard module of
`[D, χ]` have all their modes along `r_0` at least `ℓ`. The statement with `(p, q) = (0, 1)`,
`n = ℓ`, `n' = m` shows that the composite is injective; the statement with `(p, q) = (1, 0)`
is needed for the mirror composite in the other parity.

## Provenance

Internal and derived. No literature source is claimed and none is formalized. The statement is a
lemma about the harmonic analysis of `O(3)` designed for the `GL₃(ℝ)` argument above; the
section "Why the statement holds" explains why it is true.
