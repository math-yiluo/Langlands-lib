# Commutative linearly reductive groups are of multiplicative type

`Langlands.GroupScheme.CommutativeLinearlyReductiveMultiplicativeTypeStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: let `k : Type u` be a field and let
`G : GroupScheme (Spec (CommRingCat.of k))` satisfy
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. If
`IsCommMonObj G.X`, then the following two conditions are equivalent:

- for every `n : ℕ` and every `ρ : MatrixRepresentation G (Fin n)`,

  ```text
  sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤;
  ```

- `IsMultiplicativeType G`.

In words: a commutative affine group scheme `G` of finite type over `k` is
linearly reductive (every finite-dimensional representation of `G` is
semisimple) if and only if it is of multiplicative type.

The ingredients are existing declarations, used without change.

- `IsCommMonObj G.X` (Mathlib, `Mathlib.CategoryTheory.Monoidal.Mon`) says
  that the multiplication of `G` composed with the swap of the two factors of
  `G × G` is the multiplication again: `G` is commutative.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these, so quantifying over all `n` and all `ρ` covers
  all finite-dimensional representations.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `k`-algebra `A`, every point `x` of `G` with
  values in `A`, every `v ∈ W` and every `k`-linear map `ℓ : A → k`, applying
  `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is
  the set of vectors of `Aⁿ` all of whose images under such `ℓ` lie in `W`,
  this says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to
  `x⁻¹` gives equality. So the stable subspaces are exactly the subspaces
  stable under `G` in Milne's sense, that is, the subrepresentations.
- The set inside `sSup` is the set of simple subrepresentations of `ρ`:
  nonzero stable subspaces `W` whose only stable subspaces contained in `W`
  are `0` and `W`. A subrepresentation of the representation on `W` is the
  same as a stable subspace of `kⁿ` contained in `W`. So the first condition
  says that every `kⁿ` is the sum of its simple subrepresentations. For
  `n = 0` it holds trivially (the empty sum).
- `IsMultiplicativeType G` (from
  [`Torus.MultiplicativeType`](MultiplicativeType.md)) says that there are a
  field `K : Type u` with `Algebra k K`, a finitely generated commutative
  group `Λ : Type u` and an isomorphism of group schemes from the base change
  of `G` along `Spec.map (CommRingCat.ofHom (algebraMap k K))` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ` (from
  [`Torus.Diagonalizable`](Diagonalizable.md)), the diagonalizable group
  `D(Λ) = Spec K[Λ]`.

The commutativity hypothesis is needed only for the implication from the
first condition to the second; a group of multiplicative type is commutative
in any case.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Proposition 12.54, printed p. 248: "A commutative algebraic
group is linearly reductive if and only if it is of multiplicative type."

Definition 12.52 (same page): "An algebraic group is linearly reductive if
every finite-dimensional representation is semisimple."

Conventions used:

- Notations, printed p. 3: "An algebraic scheme over k (or algebraic
  k-scheme) is a scheme of finite type over k". Printed p. 6: "An algebraic
  group over k is a group object in the category of algebraic schemes over
  k." Opening of Chapter 12, printed p. 230: "Recall that all algebraic groups
  are affine over a base field k."
- Definition 1.24, printed p. 12: "An algebraic group (G, m) is commutative
  if m ∘ t = m, where t is the transposition map".
- Representations. Chapter 4 opens, printed p. 83, with "Throughout this
  chapter, G is an affine algebraic group over a field k." On the same page:
  "A linear representation of G is a homomorphism r: G → GL_V of
  group-valued functors. When V is finite-dimensional, r is a homomorphism of
  algebraic groups." Printed p. 41: "If V has finite dimension n, then the
  choice of a basis for V determines an isomorphism GL_V → GL_n".
- Subrepresentations. Proposition 4.3, printed p. 85, describes the
  stabilizer `G_W` of a subspace `W` by the functor
  `R ⇝ {g ∈ G(R) | g(W_R) = W_R}`, and the proof of Corollary 4.4 (same
  page) reads "G_W = G, i.e., W is stable under G". The proof of Corollary 4.8, printed p. 86,
  states: "A subspace W of V is stable under G if and only if it is an
  O(G)-subcomodule of V". These subspaces are the subrepresentations.
- Semisimple. Definition 4.15, printed p. 90: "A representation of an
  algebraic group is simple if it is ≠ 0 and its only subrepresentations are
  0 and itself. It is semisimple if it is a sum of simple
  subrepresentations."
- Multiplicative type. Definition 12.17, printed p. 236: "An algebraic group
  over k is of multiplicative type if it becomes diagonalizable over some
  field containing k." Definition 12.7, printed p. 233: "An algebraic group G
  is diagonalizable if the group-like elements in O(G) span it as a k-vector
  space." Theorem 12.8 (same page): "An algebraic group G is diagonalizable if
  and only if it is isomorphic to D(M) for some commutative group M." Theorem
  12.9(a) (same page): "The functor M ⇝ D(M) is a contravariant equivalence
  from the category of finitely generated commutative groups to the category
  of diagonalizable algebraic groups".

The provenance is derived for these reasons:

- The group. Milne's `G` is a commutative affine group scheme of finite type
  over `k`. The Lean statement assumes `[IsAffineHom G.X.hom]` (the
  affineness convention of Chapter 12) and `[LocallyOfFiniteType G.X.hom]`;
  since `Spec k` is quasi-compact and `G` is affine over it, the two together
  say that `G` is of finite type over `k`. Commutativity is Definition 1.24:
  `IsCommMonObj G.X` is the equation `m ∘ t = m` in the category of schemes
  over `Spec k`.
- Linearly reductive. Every finite-dimensional representation `(V, r)` is
  isomorphic, after the choice of a basis of `V`, to a homomorphism
  `G → GL_n`, and an isomorphism of representations carries simple
  subrepresentations to simple subrepresentations. So Definition 12.52 is
  the first condition, which is Definition 4.15 for every representation on
  `kⁿ`: a sum of simple subrepresentations is the supremum of the set of
  simple subrepresentations.
- Multiplicative type. `IsMultiplicativeType G` asks that `G_K ≅ D(Λ)` for
  some field `K` containing `k` and some finitely generated `Λ`. For an
  algebraic group, "diagonalizable over `K`" (Definition 12.7) means, by
  Theorems 12.8 and 12.9(a), `G_K ≅ D(Λ)` with `Λ = X(G_K)` finitely
  generated, so asking for finitely generated `Λ` is no restriction.
- `k`, `G`, `K`, `Λ` and the test algebras in `IsStableSubspace` lie in one
  universe `u`. This is a formalization convention.

Milne's proof, printed p. 249: "We saw in (12.30) that Rep(G) is semisimple
if G is of multiplicative type. Conversely, if Rep(G) is semisimple, then
Hom(G, U_2) = 0. But U_2 ≃ Ga, and so G is of multiplicative type by
(12.18)." Here `U_2` is the group of upper unitriangular `2 × 2` matrices
(2.9, printed p. 42: "U_n: R ⇝ {(a_ij) | a_ij = 0 for i > j, a_ij = 1 for
i = j}"), and `Rep(G)` is the category of
finite-dimensional representations of `G` (printed p. 165, in the paragraph
headed "Notes" after the proof of Theorem 9.2).

Relation to the Library. Apart from this module, the Library has no statement
of Proposition 12.54; its notion of linear reductivity, `IsLinearlyReductive`
(in [`NagataReductionStatements`](NagataReductionStatements.md)), is the first
condition above. Its
`CharZeroReductiveSemisimpleRepresentationStatement` (in
[`Reductive.SemisimpleRepresentationCharZeroStatement`](../Reductive/SemisimpleRepresentationCharZeroStatement.md),
Milne's Theorem 22.42) uses the same semisimplicity condition for connected
groups in characteristic zero.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Definition 12.52 on
printed p. 248 and Proposition 12.54 and its proof on printed p. 249, with the
same wording.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 12, corrections on p. 244 (12.41) and p. 249 (proof of 12.57) only;
the p. 249 entry concerns Theorem 12.57, not Proposition 12.54. Its p. 85
entry (listed under the Chapter 3 heading) says that `G_W` is the stabilizer
of `W` in `G` (not `V`), a wording correction to Proposition 4.3 that does not
change the notion of stable subspace. Its Chapter 4 entry (p. 95, proof of
4.29) does not concern the passages used, and it has no entry for printed
pp. 3, 6, 12, 41, 42, 83, 86, 90, 165, 230, 233, 236 or 248. The errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 12, one entry, on p. 234 (Example 12.10), and for Chapter 4 one
entry, on p. 89 (proof of 4.14). Neither these nor its other entries (the
nearest are on pp. 7, 13 and 15 of Chapter 1, and on A.64) concern the
passages used.

## For the proof (not part of this module)

The Library proves the statement as
`Langlands.GroupScheme.commutativeLinearlyReductiveMultiplicativeType` in
[`LinearlyReductiveMultiplicativeTypeProof`](LinearlyReductiveMultiplicativeTypeProof.md).

- Multiplicative type implies linearly reductive. This is the first part of
  Milne's Theorem 12.30 ("Rep(G) is semisimple"). Its Lean form is
  `MultiplicativeTypeRepresentationGaloisOrbitStatement` (in
  [`Rational.MultiplicativeTypeRepresentationStatement`](../Rational/MultiplicativeTypeRepresentationStatement.md)),
  proved as `multiplicativeTypeRepresentationGaloisOrbit` in
  [`Rational.MultiplicativeTypeRepresentationProof`](../Rational/MultiplicativeTypeRepresentationProof.md). Its first
  conjunct, applied with a separable closure `Ks` of `k` in universe `u`
  (for example `SeparableClosure k`), is exactly the first condition. It
  assumes only `[IsAffineHom G.X.hom]` and `IsMultiplicativeType G`.
- Linearly reductive implies multiplicative type, for commutative `G`. Let
  `u : G ⟶ 𝔾ₐ` be a homomorphism, `𝔾ₐ = VectorGroup.groupScheme (CommRingCat.of k) 1`.
  Compose it with the homomorphism `𝔾ₐ → GL_2`, `a ↦ [[1, a], [0, 1]]`
  (the isomorphism `𝔾ₐ ≅ U_2`), to get `ρ : MatrixRepresentation G (Fin 2)`.
  The line `k e₁` is stable. Let `f ∈ O(G)` be the coordinate of `u` at the
  universal point; it is primitive, so `ε(f) = 0`. If `f ≠ 0`, then `f` is
  not a constant, so some `k`-linear `ℓ : O(G) → k` has `ℓ(1) = 0` and
  `ℓ(f) = 1`. For a stable `W` containing a vector `(a, b)` with `b ≠ 0`,
  applying `ℓ` to `ρ(x)(a, b) = (a + f b, b)` at the universal point `x`
  gives `(b, 0) ∈ W`, so `W = k²`. Hence `k e₁` is the only simple stable
  subspace, and the supremum is `k e₁ ≠ k²`, contradicting the first
  condition. So `f = 0` and `u` is trivial. Since every homomorphism
  `G ⟶ 𝔾ₐ` is trivial, `G` satisfies condition (b) of Milne's Theorem 12.18,
  which implies (a), multiplicative type. Theorem 12.18 is
  `MultiplicativeTypeCharacterizationStatement` (in
  [`MultiplicativeTypeCharacterizationStatement`](MultiplicativeTypeCharacterizationStatement.md)),
  proved as `multiplicativeTypeCharacterization` in
  [`MultiplicativeTypeCharacterizationProof`](MultiplicativeTypeCharacterizationProof.md). A proof must construct the
  homomorphism `𝔾ₐ → GL_2` and the correspondence between homomorphisms
  `G ⟶ 𝔾ₐ` and primitive elements of the coordinate algebra.
