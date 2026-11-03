# Polynomial comparison with a closed algebraic embedding height: proof

`Langlands.Global.RepresentationGrowth.closedImmersionHeightDomination` proves the
published proposition
`Langlands.Global.RepresentationGrowth.ClosedImmersionHeightDominationStatement`
at its arbitrary universe `u`. The statement is unchanged and adds no hypothesis.
For every number field `F`, every group scheme `G` over `Spec F`, all natural ranks
`N` and `M` (zero included), and matrix representations

```text
rho   : G -> GL_N,
sigma : G -> GL_M,
```

such that `rho` is a closed immersion (`GroupScheme.IsClosedSubgroup rho`), there are
a real `C >= 1` and a natural `d` with

```text
height F G sigma g <= C * (height F G rho g)^d
```

for every `g : InfiniteAdelicGroupPoints F G`. The constant and the degree are chosen
before the point quantifier. The heights are the existing
`RepresentationGrowth.height`, which is the original `ArchimedeanGL.matrixHeight`:
`max 1` of the row-sum operator norms of the matrix and of its inverse, computed in
mixed real and complex coordinates. No reductivity, smoothness, connectedness,
faithfulness of `sigma` or positive rank is used.

## Route

The proof follows the route described in the statement Markdown. Two changes are made.
The matrix entries and the inverse-matrix entries of `sigma` are treated in the same
way, so no separate inversion argument is needed. The polynomial estimates are made
after the ring isomorphism to the mixed space, whose product norm is submultiplicative.

### Algebraic step

* `affinePointEvaluation_quotient`: for an affine point `y` of `GL_n` over an algebra
  `S`, and a polynomial `p` in the matrix and inverse-matrix variables `Coordinate n`,
  evaluating the regular function `ΓSpecIso.inv (quotient p)` at `y` gives
  `aeval (values g) p`, where `g = affinePointsEquiv y`. Here `values g` sends
  `entry i j` to `g i j` and `inverseEntry i j` to `g⁻¹ i j`. The proof writes
  `y` as the spectrum of `classify g` (`affinePointsEquiv_symm_apply`). It then
  applies `affinePointEvaluation_map_classify` and `classify_quotient`.
* `exists_coordinate_polynomial`: let `rho` be a closed immersion. For each variable
  `c : Coordinate m` there is a polynomial `p` in the variables of `GL_n` with the
  following property. For every algebra `S` and every point `x : G.affinePoints S`,
  the `c`-coordinate of the `sigma`-matrix of `x` equals `aeval` of `p` at the
  coordinates of the `rho`-matrix of `x`. Since `GL_n` is affine,
  `IsClosedImmersion.isAffine_surjective_of_isAffine` gives that the map `rho.appTop`
  on global regular functions is surjective. The pullback along `sigma` of the
  coordinate function of `c` therefore lifts to a regular function `t` on `GL_n`.
  `t` is the image of a polynomial, because `ΓSpecIso` is an isomorphism and the
  coordinate-ring quotient map is surjective. Evaluation at a point commutes with
  composition (`affinePointEvaluation_postcomp`, which holds definitionally).
  Applying `affinePointEvaluation_quotient` once for `sigma` (with `p = X c`) and
  once for `rho` gives the claimed equation.

### Estimates

* `PolyBounded h f` is a helper predicate: `f <= C * h^d` pointwise for some
  `C >= 0` and some natural `d`. When `h >= 1` it is closed under constants, sums,
  finite sums (`polyBounded_sum`) and multiplication by a nonnegative factor
  bounded by `h` (`PolyBounded.mul_le`), and it passes to smaller functions
  (`PolyBounded.mono`).
* `polyBounded_aeval`: let `φ` be a ring homomorphism into a normed ring, and let
  `h >= 1` bound the norm of every `φ`-image of a variable value. Then for each fixed
  polynomial `p`, `‖φ (aeval v p)‖` is `PolyBounded h`. The proof is by
  `MvPolynomial.induction_on`, using the triangle inequality for sums and
  `norm_mul_le` for multiplication by a variable. A constant `C r` has the fixed
  bound `‖φ (algebraMap r)‖`. No `NormOneClass` is needed.
* `norm_entry_le_linfty_opNorm` and `linfty_opNorm_le_sum` use
  `Matrix.linfty_opNorm_def`. They show that every entry is at most the row-sum
  operator norm, and that this norm is at most the sum of all entry norms.

### Assembly

In `closedImmersionHeightDomination`, `φ` is the ring isomorphism
`InfiniteAdeleRing.ringEquiv_mixedSpace F`. The coordinates
`archimedeanGLCoordinates F n a` of a matrix `a` are its entries mapped by `φ`,
and the same holds for the inverse matrix. Both identifications hold
definitionally. Every coordinate of the `rho`-matrix therefore has `φ`-norm at most
`height F G rho g`, by `norm_val_le_matrixHeight` and `norm_inv_le_matrixHeight`.
`infiniteMatrix F G tau g` is definitionally `affinePointsEquiv (g ≫ tau)`. So the
coordinate polynomials and `polyBounded_aeval` make every `φ`-coordinate of the
`sigma`-matrix and of its inverse `PolyBounded (height F G rho)`. Finite sums bound
the two operator norms. Then
`max 1 (max a b) <= 1 + a + b` bounds `height F G sigma`. Replacing the resulting
constant `C` by `max C 1` gives `C >= 1`; this is valid because the powers of the
height are nonnegative.

Inspection reports that the final theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The statement Markdown gives the source motivation: Getz and Hahn, *An
Introduction to Automorphic Representations* (2024), Exercise 6.1, and the
surrounding discussion of heights. This proof is an internally derived argument
for the Library's fixed mixed-space height. It does not follow a printed proof.
The helper lemmas are elementary and are stated in the generality the proof
needs.
