# Root and resultant tools for the Stepanov–Schmidt argument

Module `Langlands.AlgebraicGeometry.LangWeil.Stepanov.RootTools`. It imports only Mathlib
(`Mathlib.RingTheory.Polynomial.Resultant.Basic`, `Mathlib.RingTheory.Polynomial.GaussLemma`,
`Mathlib.FieldTheory.Finite.Basic`, `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`,
`Mathlib.FieldTheory.Separable`, `Mathlib.Algebra.Polynomial.Inductions`). All declarations are
in the namespace `Langlands.AlgebraicGeometry.LangWeil.Stepanov`, with one universe `u`.

A bivariate polynomial `p : Polynomial (Polynomial F)` is read as `p(X, Y)` with outer variable
`Y`. `Polynomial.resultant f g m n` is Mathlib's resultant: the determinant of the Sylvester
matrix of `f` and `g` with sizes `m` and `n`.

## Main results

- `resultant_ne_zero_of_not_dvd`. Let `F` be a field and `fh A : Polynomial (Polynomial F)` with
  `fh` irreducible, `1 ≤ fh.natDegree`, `A.natDegree ≤ D` and `¬ fh ∣ A`. Then
  `Polynomial.resultant fh A fh.natDegree D ≠ 0`, that is, `Res_Y(fh, A)` computed with
  Sylvester sizes `deg_Y fh` and `D` is a nonzero element of `F[X]`.
- `nonrationalRoots`. Let `F` be a finite field with `q = Nat.card F` elements and
  `p : Polynomial F` separable. There is a finite set `T` of elements `y` of
  `AlgebraicClosure F` such that, for every `y ∈ T`, `y` is a root of `p`, `y ^ q` is a root of
  `p`, and `y ^ q ≠ y`. Moreover `p.natDegree - p.roots.toFinset.card ≤ T.card` (truncated
  subtraction in `ℕ`), so `T` has at least `deg p` minus the number of distinct roots of `p` in
  `F` elements. The statement is elaborated under `open Classical in`, so the decidability
  instances inside `p.roots.toFinset` are the classical ones.
- `divX_telescoping`. Let `R` be a commutative ring, `f : Polynomial R` with
  `f.natDegree ≤ n`, and `y y' : R`. Then
  `f(y) - f(y') = (y - y') * ∑_{k < n} (divX^[k+1] f)(y) * y' ^ k`, where `divX^[k+1]` is the
  `(k+1)`-fold iterate of `Polynomial.divX`, which drops the constant coefficient and divides by
  `X`.

The binders of each theorem are those of the propositions `ResultantNeZeroOfNotDvd`,
`NonrationalRoots` and `DivXTelescoping` requested by Worker 5406 for the Task 5406 assembly,
in the same order. A check outside this module confirmed that each theorem proves the
corresponding proposition verbatim, using only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

## Auxiliary declaration

- `exists_algebraMap_eq_of_pow_card_eq`. Let `F` be a finite field (with a `Fintype`
  instance) and `K` a field that is an `F`-algebra. If `y : K` satisfies
  `y ^ Fintype.card F = y`, then `y = algebraMap F K x` for some `x : F`.

## Provenance

These three facts are inputs to the Stepanov–Schmidt method (W. M. Schmidt, *Zur Methode von
Stepanov*, Acta Arithmetica 24 (1973)) as used for the plane-curve Hasse–Weil bound. Their
exact formulations are internal to the project: Worker 5406 specified them for the Task 5406
assembly. Mathematically each is standard: (1) is the Gauss lemma together with the
nonvanishing of the resultant of coprime polynomials over a field; (2) is the counting of
Frobenius-fixed roots in the algebraic closure of a finite field; (3) is the polynomial
identity behind `f(y) - f(y') = (y - y') * g(y, y')`.

## Proof

- **`resultant_ne_zero_of_not_dvd`.** Let `K = FractionRing F[X]` and `φ : F[X] → K` the
  injective algebra map.
  - An irreducible polynomial of positive degree is primitive (`Irreducible.isPrimitive`).
    By Gauss's lemma (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`),
    `fh.map φ` is irreducible in `K[Y]`.
  - `fh.map φ` does not divide `A.map φ`. Since `fh ∣ 0`, the hypothesis gives `A ≠ 0`, so its
    content `c` is nonzero. Write `A = C c * primPart A`. Then `A.map φ = C (φ c) * (primPart A).map φ`,
    and `C (φ c)` is a unit of `K[Y]`. So a divisibility `fh.map φ ∣ A.map φ` would give
    `fh.map φ ∣ (primPart A).map φ`, then `fh ∣ primPart A` by
    `IsPrimitive.dvd_of_fraction_map_dvd_fraction_map`, and `fh ∣ A` because
    `primPart A ∣ A`. This contradicts the hypothesis.
  - Irreducible and not dividing gives `IsCoprime (fh.map φ) (A.map φ)`
    (`Irreducible.coprime_iff_not_dvd`). Hence the resultant of `fh.map φ` and `A.map φ` with
    their natural degrees is nonzero (`resultant_ne_zero`).
  - Since `φ` is injective, mapping by `φ` preserves both `natDegree`s. Write
    `D = A.natDegree + k`. Then `resultant_map_map` and `resultant_add_right_deg` give
    `φ (resultant fh A fh.natDegree D) = ((fh.map φ).coeff fh.natDegree) ^ k * resultant (fh.map φ) (A.map φ)`.
    The coefficient `(fh.map φ).coeff fh.natDegree` is `φ` of the leading coefficient of `fh`,
    hence nonzero, so the right-hand side is nonzero, and therefore so is
    the resultant over `F[X]`.
- **`exists_algebraMap_eq_of_pow_card_eq`.** Let `q = Fintype.card F`; then `q > 1`. Suppose
  `y` is not in the image of `F`. The images of the `q` elements of `F` are distinct roots of
  `X ^ q - X` in `K` (by `FiniteField.pow_card`), and `y` is another root. This gives `q + 1`
  distinct roots of a nonzero polynomial of degree `q` (`FiniteField.X_pow_card_sub_X_ne_zero`,
  `FiniteField.X_pow_card_sub_X_natDegree_eq`), contradicting `card_roots'`.
- **`nonrationalRoots`.** Fix a `Fintype` instance on `F`, so `q = Nat.card F = Fintype.card F`,
  and write `p'` for `p` mapped to `AlgebraicClosure F`.
  - `p ≠ 0`, since `0` is not separable, so `p' ≠ 0`.
  - If `y` is a root of `p'`, so is `y ^ q`. The map `y ↦ y ^ q` is the `F`-algebra
    homomorphism `FiniteField.frobeniusAlgHom F (AlgebraicClosure F)`, and evaluation of `p`
    commutes with `F`-algebra homomorphisms (`aeval_algHom_apply`).
  - Take `T` to be the distinct roots of `p'` filtered by `y ^ q ≠ y`. The first part of the
    statement holds by construction and the previous step.
  - `p'` is separable, so its roots are distinct (`nodup_roots`). It splits in the algebraic
    closure, so it has exactly `p.natDegree` distinct roots.
  - The roots of `p'` with `y ^ q = y` lie in the image of `F` by
    `exists_algebraMap_eq_of_pow_card_eq`, and these preimages are roots of `p` in `F` because
    `algebraMap` is injective. So there are at most `p.roots.toFinset.card` of them.
  - Splitting the roots of `p'` by the filter predicate (`Finset.card_filter_add_card_filter_not`)
    and subtracting gives the bound.
- **`divX_telescoping`.** Induction on `n`, generalizing `f`.
  - For `n = 0`, `f` is a constant, so both sides are `0`.
  - For `n + 1`, write `g = divX f`. Then `f = g * X + C (f.coeff 0)` (`divX_mul_X_add`) and
    `g.natDegree = f.natDegree - 1 ≤ n` (`natDegree_divX_eq_natDegree_tsub_one`). Hence
    `f(y) - f(y') = g(y) * (y - y') + y' * (g(y) - g(y'))`.
  - In the sum over `range (n + 1)`, the `k = 0` term is `g(y)` (`Finset.sum_range_succ'`). For
    the other terms, `divX^[k+2] f = divX^[k+1] g`, so each term is `y'` times the `k`-th term
    of the sum for `g`.
  - The induction hypothesis for `g` then closes the goal by `linear_combination`.
