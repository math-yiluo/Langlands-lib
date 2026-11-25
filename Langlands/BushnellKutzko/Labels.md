# The label sets of Bushnell–Kutzko 1994

Source: C. J. Bushnell and P. C. Kutzko, *Simple types in GL(N): computing conjugacy
classes*, in *Representation theory and analysis on homogeneous spaces*, Contemp. Math. 177
(1994), 107–135 (registered literature `bushnell-kutzko-1994-simple-types-conjugacy-classes`;
PDF page of the proceedings volume = printed page + 13). Cited below as BK94.

- `𝔍(M, k)` and (1.13): printed pp. 115–116.
- `e(p)`, `d(p)`, `f(p)`: printed p. 116, after (1.13).
- `P_n` and `P̃_n(a, b; q)`: printed p. 125, before (3.7).
- `P̃_0(a, b; q) = 𝔍(b, q)`: printed p. 126, in the paragraph after (3.7).

These are combinatorial sets: they involve only finite fields and polynomials. BK94 uses
them to count conjugacy classes of simple strata ((1.14)), simple characters ((2.5)) and
simple types ((3.7), (3.8)); none of that theory is used or formalised here.

## The fields `𝔽_{q^D}`

BK94 identifies isomorphic finite fields and writes `𝔍(M, q^D) = 𝔍(M, 𝔽_{q^D})`. Here the
fields are the family used for the polar-part number `polarPartCount`, imported
from `Langlands.Correspondence.HenniartPolarPart` (namespace `Langlands.Henniart.Numerical`):

- `polarBaseField q = GaloisField q.minFac (q.factorization q.minFac)`; for `q = p ^ k` a prime
  power (`k ≥ 1`) this is `GaloisField p k`, a field with `q` elements;
- `polarExtensionField q D = FiniteField.Extension (polarBaseField q) q.minFac D` for `D ≥ 1`,
  Mathlib's chosen extension of degree `D` of `polarBaseField q`; it has `q ^ D` elements.

The imported fields need `Fact q.minFac.Prime`, and `polarExtensionField q D` also needs
`NeZero D`. To give every natural `q` an ambient label type, define
`labelFieldSize q := if q = 1 then 2 else q` and use
`polarExtensionField (labelFieldSize q) D`, with `D : ℕ+`. The supplied instance
`labelFieldSize_minFac_prime` follows from `labelFieldSize q ≠ 1` and
`Nat.minFac_prime`. For every prime power `q`, `q ≠ 1`, so `labelFieldSize q = q` and these
are precisely the fields of `HenniartPolarPart`. In particular `𝔽_q` is the degree-one extension
`polarExtensionField q 1`, also used for `f = 1` there. At `q = 1` the arbitrary
ambient fields are the degree-`D` extensions for parameter `2`; the label sets are empty
by their `IsPrimePow q` guards. They are likewise empty for every other non-prime-power
`q`. This convention extends BK94, which only uses prime powers.
The fields for different `D` are separate types; no embedding between them is chosen or
needed for the definitions.

## The polynomial sets `𝔍(M, k)`

`𝔍(M, k)` is the set of monic irreducible polynomials in `k[X]` of degree `M`, with `X`
removed when `M = 1` (BK94, printed p. 115). It is
`Langlands.FieldTheory.irreduciblePolynomialLabels M k`, published in the module
`Langlands.FieldTheory.IrreduciblePolynomialLabels` and imported here; this module does not
define a second copy. That definition is
`{P | P.Monic ∧ Irreducible P ∧ P.natDegree = M} \ {X}`; it is used here only with
`k = polarExtensionField (labelFieldSize q) D`.

## Labels: encoding of the quadruple sequences of (1.13)

BK94 (1.13): given integers `m < n`, positive integers `a`, `b` and a prime power `q`,
`P^m_n(a, b; q)` is the set of finite sequences of quadruples
`p = ((φ_i(X), n_i, d_i, e_i))_{0 ≤ i ≤ r}` with `r ≥ 0` such that

- (i) `n_i` is an integer and `d_i`, `e_i` are positive integers;
- (ii) (a) `n_0 = n`, (b) `d_0 ∣ b`, (c) `e_0 = gcd(n_0, a)`, (d) `φ_0 ∈ 𝔍(d_0, q)`;
- (iii) for `1 ≤ i ≤ r`: `m < n_i < n_{i−1}`, `d_0 d_1 ⋯ d_i ∣ b`, `e_i = gcd(n_i, e_{i−1})`
  and `φ_i ∈ 𝔍(d_i, q^{d_0 d_1 ⋯ d_{i−1}})`.

Lean encoding:

- `FieldPolynomial q` is a pair of an exponent `D : ℕ+` and a polynomial in
  `(polarExtensionField (labelFieldSize q) D)[X]`, i.e. a polynomial over `𝔽_{q^D}` recorded together with
  `D`. The field of `φ_i` depends on the earlier degrees, so the type of `φ_i` has to be
  recorded with it.
- `LabelEntry q` is one quadruple `(φ_i, n_i, d_i, e_i)`: the fields are
  `polynomial = (D, φ_i)`, `level = n_i`, `degree = d_i`, `ramification = e_i`.
- `Label q` is a structure with the last index `r : ℕ` and the entries
  `entry : Fin (r + 1) → LabelEntry q`, indexed by `0 ≤ i ≤ r`. Two labels are equal exactly
  when they have the same `r` and the same entries.
- `Label.degreeProd p i` is the partial product `d_0 d_1 ⋯ d_{i−1}` over the entries of index
  `< i` (the empty product `1` when `i = 0`).

`labelSet m n a b q` is `P^m_n(a, b; q)`. Its conditions, in order:

- `IsPrimePow q ∧ m < n ∧ 0 < a ∧ 0 < b`: the range in which BK94 defines the set. Outside it
  the set is empty (a documented convention; BK94 only uses this range).
- (i): `0 < d_i` and `0 < e_i` for all `i`.
- (ii): `n_0 = n`, `d_0 ∣ b`, `e_0 = gcd(n_0, a)`, the field exponent of entry `0` is `1`, and
  `φ_0 ∈ 𝔍(d_0, polarExtensionField (labelFieldSize q) 1)`, i.e. `φ_0 ∈ 𝔍(d_0, 𝔽_q)`.
- (iii), stated for the entry of index `i + 1` with `i : Fin r` (so `1 ≤ i + 1 ≤ r`):
  `m < n_{i+1}`, `n_{i+1} < n_i`, `degreeProd p (i + 2) = d_0 ⋯ d_{i+1}` divides `b`,
  `e_{i+1} = gcd(n_{i+1}, e_i)`, the field exponent of entry `i + 1` is
  `degreeProd p (i + 1) = d_0 ⋯ d_i`, and
  `φ_{i+1} ∈ 𝔍(d_{i+1}, polarExtensionField (labelFieldSize q) (d_0 ⋯ d_i))`, i.e.
  `φ_{i+1} ∈ 𝔍(d_{i+1}, 𝔽_{q^{d_0 ⋯ d_i}})`.

All sets below are defined for every natural `q`, with no instance argument on `q`. The
condition `IsPrimePow q` makes each set empty whenever `q` is not a prime power, including
`q = 0` and `q = 1`.

**Bijection with BK94's set.** The levels are natural numbers. This loses nothing for
`m ≥ 0`, which is the only case needed here: (ii) and (iii) give `n_0 = n > m ≥ 0` and
`n_i > m ≥ 0`, so every level of an element of `P^m_n(a, b; q)` is a natural number. (BK94
allows any integers `m < n`; negative `m` is not covered.) The field exponents are forced
by the conditions (`1` for entry `0`, `d_0 ⋯ d_{i−1}` for entry `i`; these are positive by
(i)), so `polarExtensionField (labelFieldSize q) D` is the field `𝔽_{q^D}` of (1.13). Forgetting the field
exponents therefore identifies `labelSet m n a b q` with BK94's `P^m_n(a, b; q)` for natural
`m < n`, positive `a`, `b` and prime powers `q`, once each `𝔽_{q^D}` is taken to be
`polarExtensionField (labelFieldSize q) D`. The degrees `d_i` and the numbers `e_i` are
kept as data, exactly as in BK94, even though `d_i` is the degree of `φ_i` and the `e_i`
are determined by the levels and `a`.

## The functions `e`, `d`, `f` (BK94, printed p. 116)

For a label `p`:

- `Label.e p = e_r`, the `ramification` of the last entry;
- `Label.d p = d_0 d_1 ⋯ d_r`, the product of all degrees;
- `Label.f p b = b / d(p)`. BK94 writes `f(p) = b / d(p)`; the dependence on `b` is
  implicit there and explicit here. For `p ∈ P^m_n(a, b; q)`, `d(p)` divides `b` (by (ii)(b)
  when `r = 0` and by (iii) for `i = r` otherwise), so the natural-number division is exact.

## `P_n`, `P̃_n` and `P̃_0` (BK94, printed pp. 125–126)

- `bottomLabelSet n a b q = labelSet 0 n a b q` is `P_n(a, b; q) = P^0_n(a, b; q)`. BK94
  defines it for `n > 0`; for `n = 0` it is empty, since `labelSet` requires `m < n`.
- `extendedLabelSet n a b q` is
  `P̃_n(a, b; q) = {(p, φ(X)) : p ∈ P_n(a, b; q), φ(X) ∈ 𝔍(f(p), q^{d(p)})}`. Its elements
  are pairs `(p, (D, φ))` with `p ∈ P_n(a, b; q)`, `D = d(p)` and
  `φ ∈ 𝔍(f(p), polarExtensionField (labelFieldSize q) D)`. The exponent `D` is forced to be `d(p)` (which is
  positive), so forgetting it identifies the set with BK94's `P̃_n(a, b; q)`. For `n = 0` it is
  empty; BK94's `P̃_0` is the next definition.
- `degenerateLabelSet b q` is `P̃_0(a, b; q) = 𝔍(b, q)`, a set of polynomials over
  `polarExtensionField (labelFieldSize q) 1 = 𝔽_q`. It does not depend on `a`, so `a` is not an argument. It is
  empty when `q` is not a prime power.
