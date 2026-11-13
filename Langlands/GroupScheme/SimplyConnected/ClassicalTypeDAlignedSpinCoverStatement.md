# Spin covers aligned with a numbered type-D diagram

Author: Worker 64.

`Langlands.GroupScheme.ClassicalTypeDAlignedSpinCoverStatement.{u}` is
an **unproved** statement. It is the existence half of
`ClassicalTypeDSpinPresentationStatement`. The theorem
`classicalTypeDSpinPresentation_of_aligned` derives that statement from
this one and from `AlignedSpinCoverTitsIndexStatement`. It holds over
every field, in every characteristic, for every absolute rank `n ≥ 4`,
and it assumes no algebra, involution, form or cover as input.

## Hypotheses

These are the hypotheses of `ClassicalTypeDSpinPresentationStatement`,
word for word:

- `K : Type u` is a field and `G` is an affine, locally finite type group
  scheme over `Spec K` with an actual index `d : TitsIndexData G`;
- `e : d.Vertex ≃ Fin n` with `4 ≤ n` preserves every Cartan entry of
  `CartanMatrix.D n`;
- `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`;
- for every `γ : K^s ≃ₐ[K] K^s` and every vertex `a` with
  `(e a).val + 2 < n`, `d.star γ a = a`.

The star condition allows inner type `D`, the outer type `²D` and, for
`D₄`, a swap of the two arms other than the one at vertex `0`.
Trialitarian `D₄` is excluded.

## Conclusions

There exist a central finite dimensional division algebra `D : Type u`
over `K`, natural numbers `degree` and `m`, an involution
`σ : Quaternionic.FirstKindInvolution K D`, a form
`q : σ.QuadraticForms (Fin m)` and a morphism `π : G ⟶ σ.isometryGroup q`
with:

- `0 < degree`, `Module.finrank K D = degree ^ 2`, `m * degree = 2 * n`;
- `Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2`
  (natural-number division, Tits's type-1 convention);
- `σ.IsNondegenerateQuadratic q`;
- `σ.IsSpinCover q π`;
- **alignment**: for every vertex `v` with `(e v).val = 0`,
  `d.FundamentalWeightTrivialOnKernel v π`. That is, the fundamental
  weight at vertex `0` is trivial on `ker π ∩ T` over `K^s`, read through
  all `K^s`-scheme points.

The conclusion asserts nothing about the Witt index or the distinguished
vertices. Those comparisons are `AlignedSpinCoverTitsIndexStatement`.

## Mathematical content

This section describes the expected proof; none of it is carried out in
Lean. The spin cover must have its vector vertex at the vertex numbered
`0` (see `SpinCoverFundamentalWeight.md`). For `n ≥ 5` every spin cover
has this property. For `D₄` triality permutes the three end vertices, so
the alignment is a real condition. The proof must

1. realize `G` as `Spin(A, σ_A, f_A)` for a central simple `K`-algebra `A`
   of degree `2n` with a quadratic pair `(σ_A, f_A)`, with vector vertex
   `0`. By KMRT Definition (5.4) and the discussion after it, the
   involution `σ_A` underlying a quadratic pair is orthogonal when
   `char K ≠ 2` and symplectic when `char K = 2`. `σ_A` is an involution
   of the degree-`2n` algebra `A`. It is not the involution `σ` of the
   division algebra `D` in the conclusion;
2. write `A = End_D(D^m)` with `D` central division of degree `degree`,
   choose an involution `σ` of `D` of Tits type 1 (that is,
   `dim_K Sym(σ) = degree (degree + 1) / 2`), and represent `(σ_A, f_A)`
   by a nondegenerate `σ`-quadratic form `q` on `D^m` (Tits 1968,
   §§2.2–2.3, characteristic free). In characteristic 2 a type-1 `σ` may
   be symplectic;
3. construct the actual central isogeny `G → O(q)⁰`, including
   smoothness of `O(q)`, and check the alignment.

### Step 1 in every characteristic

For `n ≥ 5`, step 1 is KMRT Theorem (26.15). Chapter VI of KMRT works
over an arbitrary field and uses quadratic pairs to include
characteristic 2. Every spin cover is then aligned at vertex `0`.

For `n = 4`, Theorem (26.15) does not apply (KMRT Remark (26.17)). KMRT
Remark (44.7) and Theorem (44.8) realize groups of type `¹D₄` and `²D₄`
as `Spin(A, σ_A)`. They are proved only in characteristic different
from 2: Chapter X assumes this at its start (printed p.547 / PDF p.570),
and its closing Notes (printed p.571 / PDF p.594) explain that the
characteristic-2 version with quadratic pairs was not worked out. The
present statement includes characteristic 2. For `D₄` the proof
therefore uses the following derived argument. It needs only results
of KMRT Chapters VI and VII that hold in every characteristic, and it
uses no triality algebras.

- (a) Let `(A₀, σ₀, f₀)` be the split algebra of degree 8 with the
  quadratic pair of a hyperbolic form, and `S₀ = Spin(A₀, σ₀, f₀)`. By
  Theorem (25.16) and Corollary (25.17), the automorphisms of `S₀` over
  `K^s` are the inner ones extended by `Aut(Dyn D₄) ≅ S₃`. The proof of
  Theorem (26.15) computes the map `(26.16)` from
  `PGO(A₀, σ₀, f₀) = Aut(A₀, σ₀, f₀)` to these automorphisms: `PGO⁺`
  maps isomorphically onto the inner automorphisms, and every element
  of the other coset induces an outer automorphism. Such an
  automorphism preserves the vector representation `S₀ → O⁺`, so it
  fixes the vector vertex and swaps the two half-spin vertices. Hence
  `PGO(A₀, σ₀, f₀)(K^s)` maps injectively onto the automorphisms whose
  image in `Aut(Dyn D₄)` fixes the vector vertex. This identification of
  the image is a derived consequence of (26.16) and is not stated in
  that form in KMRT.
- (b) Choose an isomorphism `φ : G_{K^s} ≅ S₀_{K^s}` that sends vertex
  `0` of the index to the vector vertex. The Galois 1-cocycle
  `g_γ = φ ∘ γ(φ)⁻¹` has image in `Aut(Dyn D₄)` given by the star action
  of `γ`, read through `φ`. By hypothesis the star action fixes
  vertex `0`. So every `g_γ` lies in the image of
  `PGO(A₀, σ₀, f₀)(K^s)`, and by injectivity it lifts uniquely to a
  1-cocycle there.
- (c) As in the proof of KMRT Proposition (26.2), the lifted cocycle
  twists `(A₀, σ₀, f₀)` into a central simple `K`-algebra with
  quadratic pair `(A, σ_A, f_A)` of degree 8. This uses the bijection of
  §29.F between `H¹(K, PGO(A₀, σ₀, f₀))` and such algebras, which holds
  in every characteristic. The twist of `S₀` by the same cocycle is
  `Spin(A, σ_A, f_A) ≅ G` over `K`, with vector vertex `0`.

KMRT (44.7)–(44.8) treat the three end vertices together through
trialitarian algebras. The argument above uses only the stabilizer of
the single vertex `0`, which the hypothesis fixes. This is the content
attributed to KMRT; the resulting all-characteristic `D₄` realization
is derived here and is not a quoted theorem.

## Original sources and derived formulation

- M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of
  Involutions* (1998). Registered source
  `knus-merkurjev-rost-tignol-1998-book-of-involutions`, PDF SHA-256
  `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
  All in every characteristic unless noted:
  - Definition (5.4) and the discussion after it, printed pp.55–56 /
    PDF pp.78–79 (quadratic pairs; the underlying involution is
    orthogonal if `char ≠ 2` and symplectic if `char = 2`);
  - Theorem (25.16) and Corollary (25.17), printed p.360 / PDF p.383
    (automorphisms of split simply connected groups);
  - Proposition (26.2) and Remark (26.3), printed pp.361–362 / PDF
    pp.384–385 (descent for groupoids and the twisting argument);
  - Theorem (26.15) with its proof, including the map (26.16), and
    Remark (26.17), printed pp.370–371 / PDF pp.393–394 (`Spin(A, σ, f)`
    gives an equivalence onto simply connected groups of type `D_n`,
    `n ≠ 4`; `D₄` is excluded);
  - §27.B, type `D_n`, printed p.379 / PDF p.402 (the vector character
    factors through `O⁺`);
  - §29.F, printed pp.408–409 / PDF pp.431–432 (`H¹(F, PGO(A, σ, f))`
    classifies central simple algebras of degree `2n` with quadratic
    pair);
  - Chapter X introduction, printed p.547 / PDF p.570, and the Notes,
    printed p.571 / PDF p.594 (Chapter X, including Remark (44.7) and
    Theorem (44.8), printed p.562 / PDF p.585, assumes characteristic
    different from 2). (44.7)–(44.8) are cited for comparison only.
- J. Tits, *Formes quadratiques, groupes orthogonaux et algèbres de
  Clifford* (1968): §2.1, printed p.20 / PDF p.3; §§2.2–2.3, printed
  pp.21–22 / PDF pp.4–5 (quadratic forms over `(D, σ)` and the
  division-algebra realization, characteristic free); §3, Theorem 1 and
  Remark 3, printed p.31 / PDF p.14 (Theorem 1 starts from a form of the
  orthogonal group; Remark 3 excludes `D₄` from the resulting
  classification); §4.4, printed p.39 / PDF p.22 (`Spin q` covers
  `SU(q)⁰`). Registered source `tits-1968-formes-quadratiques-clifford`,
  PDF SHA-256
  `f8da4ecd4aae5bd5bbb3bc48873f285d7ccb058d771a5e9be855c867e391c782`.
- J. Tits, *Classification of algebraic semisimple groups* (1966),
  Table II, entries `¹D_n`, `²D_n`, printed pp.56–57 / PDF pp.61–62.
  Registered source `tits-1966-classification-algebraic-semisimple`, PDF
  SHA-256
  `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`.
  Tits lists representatives of strict isogeny classes by their rational
  points. An aligned cover of the given `G` as an actual group scheme
  remains to be constructed.

This is a derived formulation. The sources classify groups up to
isomorphism by algebras with quadratic pairs. They do not state this Lean
proposition with the Library's `TitsIndexData`, `σ.QuadraticForms`,
`IsSpinCover` and functor-of-points alignment. For `D₄` in
characteristic 2, the realization at the chosen vertex is the derived
argument (a)–(c) above, not a result quoted from KMRT Chapter X.
