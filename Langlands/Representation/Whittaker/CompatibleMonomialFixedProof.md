# Compatible monomial representatives are fixed by Weyl-conjugated transpose

Author: Worker 826.

The theorem `Langlands.Whittaker.compatibleMonomialFixed` has type exactly
`Langlands.Whittaker.CompatibleMonomialFixedStatement.{uF}`. That statement is
imported unchanged from
`Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement`. It is the
monomial specialization of property (1.5) of Shalika (1974), printed p.174, to
canonical p-adic fields and the standard all-ones character. See the statement's
Markdown for the source conventions and why `h₀ = 1`.

The module also imports the published
`Langlands.Representation.Whittaker.CompatibleTorus`. From it the proof uses only
the predicate `IsCharacterCompatibleRepresentative` and the conjugation-entry lemma
`monomial_conjugate_entry`. It also imports Mathlib's
`Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations`, which supplies
`Matrix.GeneralLinearGroup.transvection`.

## Public declarations

- `weylTransposeHomeomorph_monomial_eq_of_compatible`. Take any field `F` with a
  topology making it a topological ring, a bundled character
  `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F`, `n : ℕ`, a permutation
  `w : Equiv.Perm (Fin (n + 1))` and `d : Fin (n + 1) → Fˣ`. If the monomial matrix
  `s = permutation (n + 1) F w * Iwasawa.diagonalUnits d` satisfies
  `IsCharacterCompatibleRepresentative ψ n s`, then
  `weylTransposeHomeomorph n F s = s`.
- `compatibleMonomialFixed : CompatibleMonomialFixedStatement.{uF}`. It introduces
  the prime, the p-adic field `F`, `n`, `ψ`, `w`, `d` and the compatibility premise,
  installs `F.canonicalNormedField` as the statement does, and applies the theorem
  above with `F := F.Carrier`. The statement's literal premise is by definition
  `IsCharacterCompatibleRepresentative ψ n s`, so it is passed on unchanged.

So the result holds for every field, not only p-adic fields. No premise on `w`
or on `d` beyond compatibility is used. Rank one (`n = 0`) is covered by the same
argument.

All other declarations of the module are private helpers. They are described
below in the order of the proof.

## Notation

Write `m = n + 1`. The `(i, j)` entry of `s` is `d j` when `w j = i`, and `0`
otherwise (helper `monomial_entry`, from `permutation_entry` and
`Iwasawa.diagonalUnits_val`). By the published `weylTransposeHomeomorph_entry`, the
`(i, j)` entry of `weylTransposeHomeomorph n F s` is `s j.rev i.rev`.

## Step 1: compatibility on root elements

For `a < b` in `Fin m` and `t : F`, the helper `rootElement hab t` is Mathlib's
transvection `1 + t E_(a,b)` as an element of the actual subgroup
`upperUnipotent m F`: its entries below the diagonal vanish and its diagonal
entries are one, because `a < b` (helper `rootElement_entry` gives its entries).
Its first-superdiagonal sum is `t` if `a + 1 = b` and `0` otherwise
(`rootElement_sum`, via `superdiagonal_sum_single`).

Now assume also `w a < w b`. By `monomial_conjugate_entry`, the `(i, j)` entry of
`s * x * s⁻¹` is `d (w⁻¹ i) * x (w⁻¹ i) (w⁻¹ j) * (d (w⁻¹ j))⁻¹`. For
`x = rootElement hab t`, the only possible nonzero off-diagonal entry is at
`(w a, w b)`, which lies above the diagonal, and the diagonal entries are one.
So the conjugate is again upper unipotent (`rootElement_conjugate_mem`). Its
first-superdiagonal sum is `d a * t * (d b)⁻¹` if `(w a) + 1 = w b` and `0`
otherwise (`rootElement_conjugate_sum`).

The helper `eq_of_character_mul_eq` says: if `ψ (c₁ * t) = ψ (c₂ * t)` for all `t`,
then `c₁ = c₂`. Otherwise, putting `t = x / (c₁ - c₂)` and cancelling the nonzero
value `ψ (c₂ * t)` (it has norm one) gives `ψ x = 1` for every `x`, contradicting the
bundled field `ψ.nontrivial`.

Applying the compatibility premise to the pair formed by the root element and its
conjugate, and using `standardCharacter_apply`, gives `root_coefficient_eq`: for
`a < b` with `w a < w b`,

```text
(if a + 1 = b then 1 else 0) = (if (w a) + 1 = w b then d a * (d b)⁻¹ else 0).
```

Two consequences are drawn inside the main theorem:

- (h1) If `a + 1 = b` and `w a < w b`, then `(w a) + 1 = w b` and `d a = d b`.
  The left side is `1`, so the right side cannot be the `0` branch.
- (h2) If `a < b` and `(w a) + 1 = w b`, then `a + 1 = b`. Here `w a < w b`, and the
  right side is the nonzero `d a * (d b)⁻¹`.

## Step 2: transfer to natural numbers

The proof encodes `w`, `w⁻¹` and `d` as functions on `ℕ`: `f i = w i`,
`g c = w⁻¹ c` and `D i = d i` for arguments below `m` (with junk values above).
Both `f` and `g` map `[0, m)` into itself, they are mutually inverse there, and:

- `f (l + 1) ≤ f l + 1` for `l + 1 < m`. At an ascent this is (h1); otherwise
  `f (l + 1) < f l`.
- `g (c + 1) ≤ g c + 1` for `c + 1 < m`. If `w⁻¹ c < w⁻¹ (c + 1)`, apply (h2) to these
  two places; otherwise `g (c + 1) < g c`.
- `D (l + 1) = D l` whenever `f (l + 1) = f l + 1`, by (h1).

## Step 3: block induction

`le_add_of_step` says that a function that never jumps up by more than one
between consecutive places satisfies `f j ≤ f i + (j - i)` for `i ≤ j < m`.

`block_step` is one step of the induction. Assume `a < m` and the invariant

```text
for all i < m:  i < a  ↔  m - a ≤ f i,
```

that is, `[0, a)` is carried onto the top `a` values. Put `k = g (m - 1 - a)`, the
place of the largest value not yet used. Then `a ≤ k < m`, on the block `[a, k]`
one has `f i + k = m - 1 - a + i` (so `f` increases by one at each step there and
ends at `m - 1 - a`), and the invariant holds with `k + 1` in place of `a`.
The block formula combines `le_add_of_step` for `f` (from `i` to `k`) with
`le_add_of_step` for `g` (from `f i` to `m - 1 - a`), using `f i < m - a` from the
invariant. For the new invariant, a place `i > k` with `f i ≥ m - 1 - k` would share
its value with the place `f i + k + a + 1 - m` of the block, contradicting
injectivity.

`block_reversal` runs this induction, starting from `a = 0` and descending on
`m - a`. It concludes, for every `j < m`,

```text
f (m - 1 - f j) = m - 1 - j   and   D (m - 1 - f j) = D j.
```

If `j` lies in the current block `[a, k]`, then `m - 1 - f j = a + k - j` is in the
same block, the block formula gives the first equation, and `D` is constant on
the block by the step property of `D`. Otherwise `j > k` and the induction
hypothesis applies with `k + 1`.

## Step 4: the entrywise check

Since `(w j).rev = m - 1 - w j`, Step 3 says, for every `j : Fin m`,

```text
w (w j).rev = j.rev   and   d (w j).rev = d j.
```

Compare the `(i, j)` entries of `weylTransposeHomeomorph n F s` and `s`, namely
`s j.rev i.rev` (equal to `d i.rev` if `w i.rev = j.rev`, else `0`) and
`s i j` (equal to `d j` if `w j = i`, else `0`).

- If `w j = i`, then `w i.rev = w (w j).rev = j.rev`, and both entries are
  `d (w j).rev = d j`.
- If `w j ≠ i` but `w i.rev = j.rev`, then applying the first identity at `i.rev`
  gives `w j = w (w i.rev).rev = i`, a contradiction. So both entries are `0`.

The two units agree as matrices, hence are equal (`Units.ext`).

## Relation to the source

The statement and its source normalization are those of the imported statement
pair: J. A. Shalika, *The multiplicity one theorem for GLn*, Ann. of Math. (2)
**100** (1974), 171–193, property (1.5) on printed p.174, registered as
`shalika-1974-multiplicity-one`. The proof above is a self-contained
elementary argument written for this formalization; it is not a transcription of
Shalika's argument. It uses no symmetry of `w`, equality of diagonal entries, Bruhat-cell
stability, classification or distribution result as a premise. Every such fact it
uses is derived from compatibility, as in Steps 1 to 3.

The compiled check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
