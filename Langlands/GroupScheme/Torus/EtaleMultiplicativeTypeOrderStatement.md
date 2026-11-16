# Étale groups of multiplicative type

`Langlands.GroupScheme.EtaleMultiplicativeTypeOrderStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and `p : ℕ` with
`[ExpChar k p]`, let `Ks : Type u` be a field with `[Algebra k Ks]` and
`[IsSepClosure k Ks]`, and let `G : GroupScheme (Spec (CommRingCat.of k))`
satisfy `[Etale G.X.hom]` and `[IsAffineHom G.X.hom]`. Then

```text
IsMultiplicativeType G ↔
  IsCommMonObj G.X ∧ Nat.Coprime (Nat.card (G.affinePoints (CommAlgCat.of k Ks))) p
```

In words: an étale group scheme over `k` is of multiplicative type exactly
when it is commutative and its order, the number of its `kˢ`-points, is
prime to the characteristic exponent of `k`.

The ingredients are existing declarations, used without change.

- `ExpChar k p` (Mathlib, `Mathlib.Algebra.CharP.Defs`) says that `p` is the
  characteristic exponent of `k`: `p = 1` if `k` has characteristic `0`, and
  `p` is the characteristic otherwise.
- `IsSepClosure k Ks` (Mathlib, `Mathlib.FieldTheory.IsSepClosed`) says that
  `Ks` is separably closed and separable algebraic over `k`: `Ks` is a
  separable closure of `k`.
- `Etale G.X.hom` and `IsAffineHom G.X.hom` (Mathlib) say that the structure
  morphism `G.X.left ⟶ Spec k` is étale and affine. Together they say that
  `G` is `Spec A` for an étale `k`-algebra `A`, that is
  (`Algebra.Etale.iff_exists_algEquiv_prod`), a finite product of finite
  separable field extensions of `k`; so `G` is finite over `k`.
- `IsMultiplicativeType G` (from [`MultiplicativeType`](MultiplicativeType.md))
  says that there are a field `K : Type u` with `Algebra k K`, a finitely
  generated commutative group `Λ : Type u` and an isomorphism of group
  schemes from the base change of `G` along
  `Spec.map (CommRingCat.ofHom (algebraMap k K))` onto the diagonalizable
  group `Diagonalizable.groupScheme (CommRingCat.of K) Λ`, that is,
  `D(Λ) = Spec K[Λ]` (from [`Diagonalizable`](Diagonalizable.md)).
- `IsCommMonObj G.X` (Mathlib, `Mathlib.CategoryTheory.Monoidal.Mon`) says
  that the multiplication of `G` composed with the swap of the two factors of
  `G × G` is the multiplication again: `G` is commutative.
- `G.affinePoints (CommAlgCat.of k Ks)` (from
  [`AffinePoints`](../AffinePoints.md)) is the type of morphisms
  `Spec Ks ⟶ G.X` over `Spec k`, the `Ks`-points of `G`. `Nat.card` is its
  number of elements (the type is finite here, since `G` is finite over `k`).
- `Nat.Coprime a b` (Mathlib) says `Nat.gcd a b = 1`. For `p = 1` it always
  holds.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is the last sentence of Example 12.28, printed p. 241:

"More generally, an étale group scheme over k is of multiplicative type if and
only if its order is prime to the characteristic exponent of k."

The example begins: "The algebraic group μ_n is of multiplicative type for all
n. The constant algebraic group (Z/nZ)_k is of multiplicative type if k has
characteristic 0 or it has characteristic p not dividing n. When k has
characteristic p ≠ 0, the group (Z/pZ)_k is unipotent and not of
multiplicative type." These earlier sentences are not part of the Lean
statement.

Conventions and definitions used by the source:

- "Conventions and notation", printed p. 3: "The symbol k^a denotes an
  algebraic closure of k and k^s (resp. k^i) denotes the separable (resp.
  perfect) closure of k in k^a. The characteristic exponent of k is p or 1
  according as its characteristic is p or 0." Same page: "An algebraic scheme
  over k (or algebraic k-scheme) is a scheme of finite type over k." Printed
  p. 6: "An algebraic group over k is a group object in the category of
  algebraic schemes over k." Definition 1.24, printed p. 12: "An algebraic
  group (G, m) is commutative if m ∘ t = m, where t is the transposition map".
- Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Étale group schemes, 2.15, printed p. 44: "An algebraic group over k is said
  to be étale if it is étale as a scheme over k (see A.60). Thus, the étale
  group schemes over k are the group varieties over k of dimension zero. …
  The order of an étale group scheme G over k is the order of the abstract
  group G(k^s)." In 2.14 (same page), the order o(G) of a finite algebraic
  group is "the dimension of O(G) as a k-vector space".
- A.60, printed p. 580: "A scheme X finite over k is said to be étale over k if
  it satisfies each of the following equivalent conditions: (a) the k-algebra
  O(X) is étale (recall that X is affine); (b) X is smooth; (c) X is
  geometrically reduced; (d) X is an algebraic variety." A.61 (same page):
  "The following conditions on an algebraic scheme X over k are equivalent:
  (a) X is étale over k; (b) X is an algebraic variety over k of dimension
  zero; (c) the space |X| is discrete and the local rings O_{X,x} for x ∈ |X|
  are finite separable field extensions of k."
- Definition 12.17, printed p. 236: "An algebraic group over k is of
  multiplicative type if it becomes diagonalizable over some field containing
  k." Diagonalizable groups are the groups `D(M)` (Theorem 12.8, printed
  p. 233: "An algebraic group G is diagonalizable if and only if it is
  isomorphic to D(M) for some commutative group M"), with `M` finitely
  generated (Theorem 12.9(a), same page).

The provenance is derived for these reasons.

- Commutativity is added. As printed, the "if" direction is false: the
  constant group `S_3` over `ℚ` is étale of order `6`, which is prime to the
  characteristic exponent `1`, but it is not commutative, while a group of
  multiplicative type is commutative (it becomes isomorphic to the
  commutative group `D(M)` over a field extension, and commutativity of `G`
  can be checked after a field extension). Milne's examples in the same
  passage, `μ_n` and `(Z/nZ)_k`, are commutative. The Lean statement adds
  commutativity on the right-hand side: of multiplicative type if and only if
  commutative and of order prime to `p`. For commutative `G` this is Milne's
  sentence; the "only if" direction is Milne's, together with the
  commutativity of groups of multiplicative type. The 2022
  corrected reprint and both errata snapshots keep the sentence as printed
  (see below).
- Étale group schemes. Milne's étale group scheme is an algebraic group,
  hence of finite type and (in Chapter 12) affine, which is étale over `k`.
  The Lean hypotheses `[Etale G.X.hom]` and `[IsAffineHom G.X.hom]` describe
  the same objects: étale morphisms are locally of finite presentation, and
  an affine morphism is quasi-compact, so `G` is of finite type; conversely,
  an étale algebraic scheme is quasi-compact with discrete underlying space
  and finite separable local rings (A.61(c)), so it is finite over `k`, hence
  affine. For a
  finite `k`-scheme, Mathlib's étaleness is condition (a) of A.60 (an étale
  `k`-algebra is a finite product of finite separable field extensions).
- Order. The order is Milne's order of an étale group scheme, the number of
  elements of `G(k^s)` (2.15). For the affine `G`, `G(k^s)` is the set of
  `k`-algebra maps `O(G) → k^s`, equivalently of morphisms
  `Spec k^s → G` over `k`, which is `G.affinePoints (CommAlgCat.of k Ks)`
  with the chosen separable closure `Ks`. The number does not depend on the choice of
  `Ks`, since separable closures are isomorphic over `k`. It equals
  `dim_k O(G)`, the order of 2.14, because `O(G) ⊗ Ks` is a product of copies
  of `Ks` for an étale `k`-algebra `O(G)`.
- Characteristic exponent. Milne's characteristic exponent is Mathlib's
  `ExpChar k p`; the variable `p` is universally quantified with this
  instance, so it is the characteristic exponent.
- One universe `u` is used for `k`, `Ks` and the schemes. This is a
  formalization convention.

Milne gives no proof of the sentence.

Relation to the Library. The Library has no statement of Example 12.28.
Related declarations:

- `DiagonalizableSmoothConnectedCriteriaStatement` (in
  [`DiagonalizableSmoothConnectedCriteriaStatement`](DiagonalizableSmoothConnectedCriteriaStatement.md),
  Milne's Remark 12.5, proved as
  `Diagonalizable.diagonalizableSmoothConnectedCriteria` in
  [`DiagonalizableSmoothConnectedCriteriaProof`](DiagonalizableSmoothConnectedCriteriaProof.md))
  says that `D(Λ)` is smooth exactly when `Λ` has no nonzero element killed by
  `p`.
- `MultiplicativeTypeCharacterizationStatement` (in
  [`MultiplicativeTypeCharacterizationStatement`](MultiplicativeTypeCharacterizationStatement.md),
  Milne's Theorem 12.18) characterizes multiplicative type by commutativity
  together with `Hom(G, 𝔾ₐ) = 0`, or by splitting over `Ks`.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Example 12.28 on
printed p. 241 with the same last sentence. Its second sentence reads "The
constant algebraic group (Z/nZ)_k is of multiplicative type if the
characteristic of k does not divide n." The reprint has the same wording for
the conventions on printed p. 3, for 2.14 and 2.15 on printed p. 44, for
Definition 12.17 on printed p. 236 and for A.60 and A.61 on printed p. 583.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) has no
entry for printed pp. 3, 6, 12, 44, 230, 233, 236, 241 or 580. The errata
snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has no
entry for printed pp. 3, 44, 236, 241 or 583.

## For the later proof (not part of this unit)

A proof of the Lean statement can follow these steps. Write `A = O(G)`, an
étale `k`-algebra, and `m = Nat.card (G.affinePoints (CommAlgCat.of k Ks))`.

- Order. `A ⊗ Ks` is a product of `dim_k A` copies of `Ks`, so
  `m = dim_k A`, and `m` is the dimension of the coordinate ring of every base
  change of `G` to a field.
- (⇒), commutativity. If the base change `G_K` is isomorphic to `D(Λ)`, it is
  commutative. The two morphisms `m ∘ t` and `m` of `G × G ⟶ G` become equal
  after base change along `Spec K ⟶ Spec k`; on coordinate rings this is
  equality of two maps `A → A ⊗ A` after `⊗ K`, and `A ⊗ A → (A ⊗ A) ⊗ K`
  is injective.
- (⇒), order. `G_K ≅ D(Λ)` is étale over `K`, so `K[Λ]` is finite-dimensional
  and `Λ` is finite with `|Λ| = m`. Étale implies smooth, so `Λ` has no
  element of order `p` (`DiagonalizableSmoothConnectedCriteriaStatement`,
  conjunct 2); by Cauchy's theorem `p` does not divide `|Λ|` when `p` is
  prime, and for `p = 1` there is nothing to prove.
- (⇐). Suppose `G` is commutative and `m` is prime to `p`. Over `Ks`,
  `A ⊗ Ks` is the algebra of `Ks`-valued functions on the finite commutative
  group `M = G(Ks)` of order `m`, so `G_Ks` is the constant group of `M`.
  Since `m` is invertible in `k`, `X^m - 1` is separable, so `Ks` contains `m`
  distinct `m`-th roots of unity, and the dual group
  `M^∨ = Hom(M, Ksˣ)` has order `m`. Evaluation gives a map of Hopf algebras
  `Ks[M^∨] → Ks^M`; it is injective by linear independence of characters,
  hence bijective by dimension. So `G_Ks ≅ D(M^∨)` with `M^∨` finite, and
  `IsMultiplicativeType G` holds with `K = Ks`.
