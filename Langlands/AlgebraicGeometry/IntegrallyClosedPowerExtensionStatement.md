# Extending sections whose power extends, on normal integral affine schemes

`Langlands.AlgebraicGeometry.IntegrallyClosedPowerExtensionStatement.{u}` is
a proposition definition. This module defines the proposition and proves
nothing.

## Statement

Let `X : Scheme.{u}` be integral (`[IsIntegral X]`) and affine
(`[IsAffine X]`), with `IsIntegrallyClosed Γ(X, ⊤)`. Let `U : X.Opens` be
nonempty, let `f : Γ(X, U)` and `d : ℕ` with `1 ≤ d`, and suppose that
`f ^ d` is the restriction `X.presheaf.map (homOfLE le_top).op g` of some
`g : Γ(X, ⊤)`. Then `f` is the restriction of some `h : Γ(X, ⊤)`.

All ingredients are from Mathlib:

- `IsIntegral X` says that `X` is nonempty and that `Γ(X, V)` is an integral
  domain for every nonempty open `V`; `IsAffine X` says that `X` is affine.
- `IsIntegrallyClosed Γ(X, ⊤)` says that the ring of global sections, an
  integral domain, is integrally closed in its field of fractions.
- `Γ(X, U)` is the ring of sections over `U`, and
  `X.presheaf.map (homOfLE le_top).op : Γ(X, ⊤) ⟶ Γ(X, U)` is restriction.

## Original source

J. S. Milne, *Algebraic Groups: The Theory of Group Schemes of Finite Type
over a Field* (Cambridge University Press, 2017), source ID
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`. Page
numbers are printed page numbers. The one-based PDF page is the printed page
plus 16.

- Lemma 22.23, p.469: "Let X be a normal integral affine scheme, and let U
  be a dense open subscheme of X. Let f ∈ O(U). If f^d ∈ O(X) for some
  d ≥ 1, then f ∈ O(X)."
- Its proof: "We have O(X) ⊂ O(U) ⊂ k(X). Now f ∈ k(X) and is integral over
  O(X), and so it lies in O(X)."
- A.78, p.584: "An integral domain A is said to be normal if it is
  integrally closed in its field of fractions. An algebraic scheme X over k
  is normal if O_{X,x} is normal for all x ∈ |X|. This is equivalent to
  requiring that O_X(U) be a normal integral domain for every connected open
  affine subset U of X" (followed by a reference to Milne's notes on
  commutative algebra).

The 2022 corrected reprint (source ID `milne-2022-algebraic-groups`; the
one-based PDF page is the printed page plus 11) states Lemma 22.23 on
printed p.470 as "Let X be a normal integral affine scheme, and U a dense
open subscheme of X. Let f ∈ O(U). If f^d ∈ O(X) for some d ≥ 1, then
f ∈ O(X).", with the same meaning and the same proof. Its A.78 is on p.588
with the same words.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02`
(2017 edition) and `milne-2022-algebraic-groups-errata-2026-11-04` (2022
reprint) were checked. The 2017 errata entry for p.469 concerns the proof
of Lemma 22.24 ("Expanded the proof of the crucial Lemma 22.24"), not
Lemma 22.23; they have no entry for p.584. The 2022 errata have no entry for
p.470 or p.588; their p.584 entry concerns A.64.

## Derivation from the source

- **The scheme.** "Normal integral affine scheme" is an integral affine
  scheme whose ring of global sections is normal. For an integral affine
  scheme `X = Spec A` the conditions of A.78 reduce to normality of `A`:
  `X` is connected, so `A = O_X(X)` is normal by the second sentence, and
  conversely the local rings of `X` are localizations of `A`, which are
  normal when `A` is. Milne states A.78 for algebraic schemes over a field;
  Lemma 22.23 names no base field, and the statement covers every integral
  affine scheme. Normality of `A` is `IsIntegrallyClosed Γ(X, ⊤)`.
- **The open subscheme.** `X` is irreducible, so an open subset is dense
  exactly when it is nonempty: `(U : Set X).Nonempty`.
- **The section.** Milne regards `O(X) ⊂ O(U)` through restriction, which
  is injective for an integral scheme and a nonempty `U`. "`f^d ∈ O(X)`"
  says that `f ^ d` is the restriction of a global section `g`, and the
  conclusion "`f ∈ O(X)`" says that `f` is the restriction of a global
  section `h`. The exponent satisfies `1 ≤ d`, as in the source.
- **Universes.** The scheme lives in an arbitrary universe `u`. This is a
  formalization convention.
