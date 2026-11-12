# Regular elliptic elements and the correspondence `g ↔ g'`

This module defines the matching of elements behind the local
Jacquet–Langlands correspondence between `GL_n(F)` and the unit group
of a central division algebra `D` over `F`.

## Source definitions

Badulescu 2002, *Correspondance de Jacquet-Langlands pour les corps
locaux de caractéristique non nulle*, §1 and the start of §5 (source
file `math0201117.tex`, lines 178–186 and 2767–2774), works with
`G = GL_n(F)` and `G' = GL_r(D)`. An element of `G` or `G'` is

- *semisimple régulier* if its characteristic polynomial is separable;
- *elliptique régulier* if its characteristic polynomial is irreducible
  and separable.

For `g ∈ G'` the characteristic polynomial is the reduced one. One
writes `g ↔ g'` ("`g` and `g'` correspond") if `g` and `g'` are regular
semisimple and have the same characteristic polynomial.
Deligne–Kazhdan–Vignéras (Bernstein–Deligne–Kazhdan–Vignéras 1984,
introduction, printed p.33) describe the same matching as an injection
of conjugacy classes of `G'` into those of `G`. It restricts to a
bijection between the regular elliptic classes, and their main theorem
compares characters on these classes.

This module treats the case `r = 1`, `G' = D^×`, which is the case
used in Harris 1999 §5.

## Definitions

Let `F : Type u` be a field and `n : ℕ`. Elements of `GL_n(F)` are
elements of `Langlands.GeneralLinear n F`, the units of
`Matrix (Fin n) (Fin n) F`, and `charpoly` is Mathlib's
`Matrix.charpoly`.

- `IsRegularSemisimple g`: the characteristic polynomial of `g` is
  `Polynomial.Separable`.
- `IsRegularElliptic g`: `IsRegularSemisimple g` and the characteristic
  polynomial of `g` is `Irreducible` in `F[X]`.

Now let `D : Type u` be a division ring and a finite-dimensional,
central `F`-algebra (`Algebra.IsCentral F D`).

- `IsRegular F D g'` for `g' : Dˣ`: the canonical reduced
  characteristic polynomial `Langlands.CentralSimple.reducedCharpoly
  F D g'` is separable.
- `Corresponds F D g g'` for `g : GeneralLinear n F` and `g' : Dˣ`:
  `IsRegularElliptic g`, `IsRegular F D g'`, and the characteristic
  polynomial of `g` equals the reduced characteristic polynomial of
  `g'`.

`Corresponds` asks for `g` regular elliptic, which is the
Deligne–Kazhdan–Vignéras form of the relation and Badulescu's
"correspondance faible" (Théorème 5.2, lines 2818–2826). The theorem
`corresponds_iff` below shows that for `D^×` this is the same as
Badulescu's relation `g ↔ g'` between regular semisimple elements.
Nothing about `F` beyond being a field is used. `n` is arbitrary, but
`Corresponds.eq_reducedDegree` shows that corresponding elements exist
only for `n` the reduced degree of `D`, where `dim_F D = n²`.

## Proved facts

- `reducedCharpoly_eq_minpoly_of_separable F D a`: for `a : D`, if
  `reducedCharpoly F D a` is separable, it equals `minpoly F a`.
  The minimal polynomial `q` divides the reduced characteristic
  polynomial `p` by the reduced Cayley–Hamilton theorem
  (`Langlands.CentralDivision.aeval_reducedCharpoly`). Conversely,
  the regular matrix `M` of left multiplication by `a` on a basis has
  characteristic polynomial `p ^ d`, `d` the reduced degree
  (`charpoly_leftMulMatrix_eq_reducedCharpoly_pow`), and `q(M) = 0`.
  Over an algebraic closure `Ω` of `F`, every root of `p` is a root of
  the characteristic polynomial of `M`, hence lies in the spectrum of
  `M`, hence is a root of `q` (`spectrum.subset_polynomial_aeval`).
  Because `p` is separable its roots in `Ω` are distinct, so `p`
  divides `q` over `Ω`, and then over `F`. Both are monic.
- `irreducible_reducedCharpoly_of_separable F D a`: consequently a
  separable reduced characteristic polynomial is irreducible.
- `corresponds_iff F D g g'`: `Corresponds F D g g'` holds if and only
  if `IsRegularSemisimple g`, `IsRegular F D g'` and the two polynomials
  are equal. So every regular unit of `D` is elliptic, as stated in
  the source, and only regular elliptic `g` correspond to elements of
  `D^×`.
- `Corresponds.eq_reducedDegree`: if `Corresponds F D g g'` with
  `g : GeneralLinear n F`, then `n = reducedDegree F D`. The
  characteristic polynomial has degree `n` and the reduced one has
  degree `reducedDegree F D`.

## Nonvacuity

- `exists_generalLinear_charpoly_eq p hpm hn h0`: a monic polynomial
  `p` of degree `n` with nonzero constant term is the characteristic
  polynomial of an element of `GL_n(F)`. The matrix is that of
  multiplication by the class of `X` on `F[X]/(p)` in its power basis
  (Mathlib's `AdjoinRoot.powerBasis` and `charpoly_leftMulMatrix`). Its
  determinant is `(-1)^n p(0) ≠ 0`.
- `exists_corresponds F D g' hg'`: every regular `g' : Dˣ` corresponds
  to some `g : GeneralLinear (reducedDegree F D) F`. Here `p = minpoly F
  g'` has nonzero constant term because `g' ≠ 0`.
- Concrete data `D = F`: `reducedDegree_self F` gives
  `reducedDegree F F = 1`; `isRegular_self F a` shows that every
  `a : Fˣ` is regular, since its reduced characteristic polynomial is
  `X - a`; and `exists_corresponds_self F a` gives
  `g : GeneralLinear 1 F` with `Corresponds F F g a`.

Existence of regular elements in a general `D` (for instance a
generator of a separable maximal subfield) is not proved here.
