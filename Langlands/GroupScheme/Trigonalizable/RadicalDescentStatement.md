# Statement: separable trigonalizability and descent of the geometric unipotent radical

`Langlands.GroupScheme.SeparablyTrigonalizableRadicalDescentStatement.{u} : Prop` is a
statement-only encoding of Milne, Corollary 16.31. It is over arbitrary fields, including
imperfect fields. It does not assert that the geometric radical always descends.

## Lean statement

```lean
def SeparablyTrigonalizableRadicalDescentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ((∃ (K : Type u) (_ : Field K) (_ : Algebra k K), Algebra.IsSeparable k K ∧
        IsTrigonalizable
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) ↔
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G), IsGeometricUnipotentRadical i)
```

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), registered as `milne-2017-algebraic-groups`,
`Milne--Algebraic groups, the theory of group schemes of finite type over a field (book)--2017.pdf`.
Page numbers are printed pages (PDF page = printed page + 16). The 2022 corrected reprint
is registered as `milne-2022-algebraic-groups` (PDF page = printed page + 11).

- Corollary 16.31, p.335 in both editions: “A smooth connected solvable algebraic group G over k
  becomes trigonalizable over a separable field extension of k if and only if (Gₖₐ)ᵤ is defined
  over k.” Here `kₐ` is an algebraic closure. The proof is on p.335 in 2017 and p.336 in 2022.
- Chapter 16 opening and Definition 16.1, p.324 in both editions: algebraic groups in the
  chapter are affine; a group is trigonalizable if every simple representation is
  one-dimensional, equivalently if every nonzero representation has a stable line.
- Theorem 16.6 and Notation 16.7 (pp.325–326): the unipotent part `Hᵤ` is a normal unipotent
  subgroup with quotient of multiplicative type, when such a subgroup exists. For a smooth
  connected solvable group over an algebraically closed field, 16.33(a)–(c), pp.335–336,
  provides `Hᵤ`, smooth and connected, containing every unipotent subgroup, with torus quotient.
  In this setting it is the unipotent radical.

The official errata snapshots `milne-2017-algebraic-groups-errata-2026-11-02` and
`milne-2022-algebraic-groups-errata-2026-11-04` have no entry for Corollary 16.31 or its proof
(pp.335–336). The 2017 p.324 erratum corrects “diagonalizable” to “trigonalizable” in the
paragraph preceding §16a; it does not change Definition 16.1 or the affine convention.

## Correspondence to the Lean statement

- **The ambient group.** `GroupScheme S` is `Grp (Over S)`. Smoothness and connectedness
  are explicit; the affine structure map to `Spec k` is quasi-compact, so together with
  smoothness this gives a finite-type group. In [`Absolute.Borel`](../Absolute/Borel.md),
  `IsSolvableGroupScheme G` tests abstract solvability of `G(kₐ)`. For smooth affine groups
  this agrees with solvability in the sense of a terminating scheme-derived series: the
  series is smooth and commutes with field extension by 6.19(a)–(b), its terms over `kₐ`
  have the corresponding derived groups of `kₐ`-points by 6.20(b), and a smooth affine
  group over `kₐ` with only the identity point is trivial. Here 6.19, 6.20 and 6.30 occur on
  pp.129 and 132 in both editions.
- **The extension.** The left-hand side is the separable trigonalizability clause of the
  published [`SeparablyTrigonalizableCriterionStatement`](SeparableCriterionStatement.md)
  (Milne 16.6). `Algebra.IsSeparable k K` is separability of the field extension (in
  particular, algebraicity). [`IsTrigonalizable`](../Trigonalizable.md) requires a
  nonzero vector spanning a stable line in every nonzero finite-dimensional representation.
- **The descent.** `IsGeometricUnipotentRadical i`
  ([`Rational.SemistandardIntersection`](../Rational/SemistandardIntersection.md)) requires
  `i` to be a normal closed subgroup with smooth, connected, unipotent source. Its base
  change is connected, unipotent and normal, and contains every smooth connected normal
  unipotent closed subgroup over `kₐ`. For the group in the statement, uniqueness of the geometric
  radical makes that base change exactly `(Gₖₐ)ᵤ`. Conversely, when a closed subgroup over
  `k` base changes to `(Gₖₐ)ᵤ`, smoothness, connectedness, unipotence and normality are
  reflected by the field extension, so it gives such an `i`. This is descent of the subgroup
  inside `G`, not just the existence of an abstract `k`-form for it.

Milne's proof compares the two sides using 16.6. A normal unipotent subgroup over `k` with
multiplicative-type quotient base changes to `(Gₖₐ)ᵤ` by uniqueness. In the other direction,
a descended subgroup has quotient of multiplicative type because the quotient after extension
to `kₐ` is a torus. This uses the actual quotient and its field-base-change comparison.
The Library's [`solvableTorusQuotient`](../Absolute/SolvableTorusQuotientProof.md) provides
the algebraically closed split-torus quotient with smooth connected unipotent normal kernel.
