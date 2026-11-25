# The polynomial set `𝔍(n, k)` of Bushnell–Kutzko

## Definition

For a natural number `n` and a field `k` (in any universe `u`),
`Langlands.FieldTheory.irreduciblePolynomialLabels n k : Set k[X]` is the set of
polynomials `P ∈ k[X]` that are monic, irreducible and of degree `n` (Mathlib's
`natDegree`), with the polynomial `X` removed:

```
{P | P.Monic ∧ Irreducible P ∧ P.natDegree = n} \ {X}
```

Removing `X` changes the set only when `n = 1`, because `X` has degree `1`. This is
how the source states it: "with the proviso that `φ(X) ≠ X` in the case `M = 1`".
The lemma `mem_irreduciblePolynomialLabels_iff_of_ne_one` proves that for `n ≠ 1`
the set is exactly the monic irreducible polynomials of degree `n`.

## Source

Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*, Contemp.
Math. 177 (1994), printed p. 115 (PDF p. 128 of the proceedings volume), the
paragraph just before (1.13). There `k` is a finite field and `M` is a positive
integer, and `𝔍(M, k)` is "the set of monic irreducible polynomials `φ(X) ∈ k[X]`
of degree `M`, with the proviso that `φ(X) ≠ X` in the case `M = 1`". The source
writes `𝔍(M, q) = 𝔍(M, 𝔽_q)` because it does not distinguish isomorphic finite
fields. The Lean definition takes the field itself as its argument.
Source ID `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA256
`fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.

## How the Lean definition is wider than the source

The source defines the set only for finite `k` and `M ≥ 1`. The Lean definition
uses the same formula for every field and every `n : ℕ`, so the domain is larger
but the formula is unchanged:

- For `n = 0` the set is empty (`irreduciblePolynomialLabels_zero`). The only monic
  polynomial of degree `0` is `1`, and `1` is a unit, so it is not irreducible.
- For an infinite field the set is well defined but may be infinite. No result is
  claimed about that case.

## Lemmas proved in this module

- `mem_irreduciblePolynomialLabels_iff`: membership means monic, irreducible, of
  degree `n`, and `≠ X`.
- `mem_irreduciblePolynomialLabels_iff_of_ne_one`: for `n ≠ 1` the condition `≠ X`
  can be dropped.
- `irreduciblePolynomialLabels_zero`: the set is empty in degree `0`.
- `finite_setOf_natDegree_le`: over a finite field, the polynomials of degree at
  most `n` form a finite set. The proof shows that the coefficient map to
  `Fin (n + 1) → k` is injective on that set.
- `irreduciblePolynomialLabels_finite`: over a finite field, `𝔍(n, k)` is finite.

The module imports only Mathlib's polynomial and set-cardinality files, with no
representation theory, so label-counting developments can import it without
pulling in representation theory.

## Not claimed

No count of `𝔍(n, k)` (for example via Gauss's formula
`(1/n) ∑_{d ∣ n} μ(d) q^{n/d}`) is stated or proved here. Nor is any relation to
representations of `GL_n(k)`.
