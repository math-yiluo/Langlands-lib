# Finite group schemes over a field are killed by a positive integer

Author: Worker 840.

`Langlands.GroupScheme.FiniteGroupSchemeUniformExponentStatement.{u}` is the
proposition

```lean
∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
  IsFinite G.X.hom →
  ∃ n : ℕ, 0 < n ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X), x ^ n = 1
```

The module defines a proposition; it does not prove it. It is a statement
target, and no proof is published with it.

## Exact quantifiers and objects

- `k` is an arbitrary field in universe `u`. The field may be imperfect and may
  have any characteristic, including positive characteristic.
- `G` is an arbitrary group scheme over `Spec k` in the existing Library sense:
  `Langlands.GroupScheme S` (module `Langlands.AbelianScheme.GroupScheme`) is
  the abbreviation `Grp (Over S)`, a group object in schemes over `S`. Here
  `S = Spec (CommRingCat.of k)`. `G.X : Over S` is the underlying scheme over
  `Spec k`.
- `IsFinite G.X.hom` is Mathlib's finiteness property of the structure
  morphism `G.X.left ⟶ Spec k`. This is the only hypothesis on `G`. Nothing is
  assumed about commutativity, étaleness, smoothness, reducedness,
  connectedness or the characteristic, and no geometric instances are
  installed.
- The conclusion is a single natural number `n`, chosen after `k` and `G` and
  before any test scheme. It must satisfy `0 < n`, and it must work for every
  test object `T : Over (Spec (CommRingCat.of k))` and every morphism
  `x : T ⟶ G.X` over `Spec k`.

`T` ranges over **all** schemes over `Spec k` in universe `u`: affine and
non-affine schemes, and schemes of any size. It does not range only over
spectra of `k`-algebras or over points with values in a field. A morphism
`x : T ⟶ G.X` in `Over (Spec k)` is a `T`-valued point of `G`.

The power `x ^ n` is taken in the group of `T`-points of the actual group
scheme. `open scoped CategoryTheory.MonObj` makes Mathlib's
`CategoryTheory.Hom.group` (and its underlying `CategoryTheory.Hom.monoid`) an
instance on `T ⟶ G.X`. There `f * g = lift f g ≫ μ` uses the multiplication
`μ` of `G`, and `1 = toUnit T ≫ η` is the constant point at the identity. So
`x ^ n = 1` says that the `n`th power of `x` under the group law of `G` is the
trivial `T`-point.

The inner clause `∀ T x, x ^ n = 1` is definitionally
`Langlands.GroupScheme.HasUniformPowerExponent G n`, from the module
`Langlands.GroupScheme.Rational.UnipotentPointsExponent`. A private compilation
check confirmed that the whole proposition is `Iff.rfl`-equivalent to
`∀ k [Field k] G, IsFinite G.X.hom → ∃ n, 0 < n ∧ HasUniformPowerExponent G n`.
This module does not import that file. The relation is recorded only to help a
later proof.

## Source and derived provenance

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type over
a Field*, Cambridge Studies in Advanced Mathematics 170, Cambridge University
Press, 2017 (registered source `milne-2017-algebraic-groups`).

- **Proposition 11.32**, §11.g "Finite group schemes of order n are killed by
  n", printed p. 221 (PDF p. 237): "Let `G` be a finite group scheme over `k`
  of order `n`. Then, for all `k`-algebras `R`, the order of every element of
  `G(R)` divides `n`. In other words, the `n`th power map `n_G : G → G` is
  trivial." The proposition makes no commutativity, perfectness or
  characteristic assumption. Its proof reduces to the connected case using
  Corollary 11.30 (printed p. 220, PDF p. 236), which holds over every field.
- **Paragraph 2.14**, §2.a, printed p. 44 (PDF p. 60): an algebraic group
  `G` over `k` is *finite* if it is finite as a scheme over `k`; equivalently,
  `G` is affine and `O(G)` is a finite `k`-algebra. Its *order* `o(G)` is
  `dim_k O(G)`.

The displayed proposition is **derived** from Proposition 11.32, not quoted
from it:

1. *Finiteness.* Milne's finite group scheme over `k` is one whose structure
   morphism is finite. This is `IsFinite G.X.hom`. A finite morphism is of
   finite type, so Milne's standing finite-type convention for algebraic
   groups adds no further condition.
2. *All test schemes.* Milne states the conclusion for `G(R)`, `R` a
   `k`-algebra, and rephrases it as triviality of the morphism `n_G : G → G`.
   Since `G` is affine, the Yoneda lemma on `k`-algebras identifies the two
   formulations. Triviality of the morphism `n_G` gives the conclusion for
   every `k`-scheme `T`: for `x : T ⟶ G.X`, the power `x ^ n` is the composite
   of `x` with `n_G`. It is therefore the composite of `x` with the constant
   map at the identity, which is `1`.
3. *Positivity and weakening.* The order `n = dim_k O(G)` is positive. `O(G)`
   is nonzero because the identity section `Spec k ⟶ G` gives a `k`-algebra
   map `O(G) → k`. "The order of every element divides `n`" yields `x ^ n = 1`
   with this `n`. The displayed statement keeps only the existence of some
   positive exponent. It does not say that the exponent can be the order
   `dim_k O(G)`, or that element orders divide it.

The notes on the same page say that the commutative case also holds for
locally free finite group schemes over arbitrary bases (Deligne; Tate–Oort
1970, p. 4). That general-base theorem is **not** formalized here. The base is
always the spectrum of a field.

## Use and consumer

This statement is a prerequisite of the proof of
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement`. That
proof applies it to the scheme-theoretic kernel of a central isogeny, whose
structure morphism is finite by
`Langlands.GroupScheme.IsCentralIsogeny.kernel_isFinite`. No commutativity is
assumed, so the statement applies before centrality of the kernel is used.

## Source reading record

- `milne-2017-algebraic-groups`,
  `/home/taskhub/central-library/Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  PDF pp. 60, 226, 236 and 237 were read and the fingerprint verified.
- `milne-2017-algebraic-groups-errata-2026-11-02`, the official errata page
  snapshot of 2026-11-02, SHA-256
  `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
  Its Chapter 2 entries are for pp. 48, 51 and 60. Its Chapter 11 entries are
  for p. 223 (Proposition 11.36) and p. 224 (the Verschiebung section, where
  `G` is commutative, and Definition 11.39). None of these entries concerns
  p. 44, paragraph 2.14, p. 221 or Proposition 11.32.
