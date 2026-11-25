# At most `|𝔍(n, k)|` cuspidal classes of `GL_n(k)` (statement)

## Statement

`Langlands.FiniteGeneralLinear.CuspidalClassCountBoundStatement.{u, w} : Prop` says:

> for every field `k : Type u` with `[Finite k]` and every `n : ℕ` with `0 < n`,
> `ENat.card (CuspidalClass.{u, w} n k) ≤ (irreduciblePolynomialLabels n k).encard`.

In words: for every finite field `k` and every `n ≥ 1`, the general linear group
`GL_n(k)` has at most `|𝔍(n, k)|` isomorphism classes of irreducible cuspidal
complex representations on carriers in `Type w`.

The definitions used:

- `CuspidalClass.{u, w} n k` (`Langlands/Representation/FiniteGeneralLinear/Cuspidal.lean`)
  is the set of isomorphism classes of irreducible complex representations of
  `Langlands.GeneralLinear n k` on carriers in `Type w` that are cuspidal. Cuspidal
  means no proper standard block parabolic has a nonzero vector fixed by its
  unipotent radical.
- `Langlands.FieldTheory.irreduciblePolynomialLabels n k`
  (`Langlands/FieldTheory/IrreduciblePolynomialLabels.lean`) is Bushnell–Kutzko's
  `𝔍(n, k)`: the monic irreducible polynomials of degree `n` in `k[X]`, with `X`
  removed.
- `ENat.card` and `Set.encard` are Mathlib's cardinalities with values in `ℕ∞`
  (infinite types and sets have cardinality `⊤`). The inequality therefore makes sense
  without assuming either side finite. Since `𝔍(n, k)` is finite over a finite field
  (`irreduciblePolynomialLabels_finite`), the statement implies in particular that
  there are only finitely many cuspidal classes.

Universes: the field universe `u` is quantified inside the proposition through
`k : Type u`, and `u` is a universe parameter, so the statement applies to residue
fields in any universe. The carrier universe `w` is the second universe
parameter. Universe order: `.{u, w}`.

## Source and how the statement relates to it

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*, Contemp. Math.
177 (1994), printed p. 125 (PDF p. 138), right after (3.6): "The Green
parametrisation gives us a bijection between the set of equivalence classes of
irreducible cuspidal representations of `GL(f, k_E)` and the set `𝔍(f, k_E)`."
`𝔍` is defined on printed p. 115 (PDF p. 128). Source ID
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.

The underlying theory is Green, *The characters of the finite general linear groups*,
Trans. AMS 80 (1955). There the irreducible characters of `GL(n, q)` are parametrised
by partition-valued functions on simplexes (Theorems 13 and 14, §8, printed
pp. 439–443, PDF pp. 38–42). In modern terms, the cuspidal characters of `GL(n, q)`
are the primary irreducible characters `(g^{1})` of Theorem 12 (§7, printed p. 439)
for a simplex `g` of degree `n` and the partition `{1}`. Green does not use the word
"cuspidal", and this identification is not taken from his paper. Lemma 7.7 (§7,
printed p. 439) says that there are exactly as many simplexes of degree `s` as
irreducible polynomials of degree `s`. Green's correspondence sends a simplex to the
irreducible polynomial whose roots are the nonzero field elements `ε_s^k, ε_s^{kq}, …`,
so the polynomial `X` does not occur. Source ID
`green-1955-characters-finite-general-linear`, SHA256
`ded2dbd2e6fa499b64fe4c857ddaa8daf4ee4f74eef135958e4a40a02e6cac3d`.

**This record states only the upper-bound half** of the Green parametrisation:
an inequality of cardinalities, not a bijection, and no explicit map between the two
sets. Only the upper bound is needed for the intended use, the supercuspidal
upper bound of the numerical step obtained through simple types.

The hypothesis `0 < n` is needed. For `n = 0` the group `GL_0(k)` is trivial and its
trivial representation is irreducible and (vacuously) cuspidal, so there is one
class, while `𝔍(0, k)` is empty (`irreduciblePolynomialLabels_zero`).

## Not claimed

- The reverse inequality, the bijection and the existence of cuspidal
  representations are not stated.
- No formula for `|𝔍(n, k)|` (Gauss's necklace count) is stated.
- Nothing is stated for infinite fields.
- This file states a proposition only. The proof is
  `cuspidalClassCountBound` in
  `Langlands/Representation/FiniteGeneralLinear/CuspidalClassCountBoundProof.lean`.
