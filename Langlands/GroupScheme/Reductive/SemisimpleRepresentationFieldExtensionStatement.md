# Simple and semisimple representations under extension of the base field

`Langlands.GroupScheme.SemisimpleRepresentationFieldExtensionStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for all fields `k K : Type u` with `[Algebra k K]`,
every group scheme `G : GroupScheme (Spec (CommRingCat.of k))` whose
structure morphism is locally of finite type and affine, every finite index
type `n` and every `ρ : MatrixRepresentation G n`, the following hold. Write

```text
ρK := ρ.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))
```

for the representation of `G_K` on `Kⁿ` obtained by extending scalars, and
`EndAlg := Algebra.adjoin k {C : Matrix n n k | Intertwines ρ ρ C}`.

- (a) `ρK.IsIrreducible → ρ.IsIrreducible`, and
  `IsSemisimpleRep ρK → IsSemisimpleRep ρ`.
- (b) If `ρ.IsIrreducible` and every `C : Matrix n n k` with
  `Intertwines ρ ρ C` is a scalar matrix `Matrix.scalar n c` (`c : k`), then
  `ρK.IsIrreducible`.
- (c) If `IsSemisimpleRep ρ`, and either `Algebra.IsSeparable k K` or
  `IsSemisimpleRing EndAlg ∧ Algebra.Etale k (Subalgebra.center k EndAlg)`,
  then `IsSemisimpleRep ρK`.

Here `IsSemisimpleRep` is a local abbreviation inside the statement. It takes
an implicit field `F : Type u` and an implicit group scheme `H` over
`Spec (CommRingCat.of F)`, so that it applies both to `ρ` (over `k`) and to
`ρK` (over `K`):

```text
IsSemisimpleRep σ :=
  sSup {W : Submodule F (n → F) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule F (n → F), σ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤
```

In words: let `V` be a finite-dimensional representation of an affine
algebraic group `G` over `k`, let `K` be an extension field of `k`, and let
`V_K` be the representation of `G_K` obtained by extension of scalars.

- (a) If `V_K` is simple (resp. semisimple), so is `V`.
- (b) If `V` is simple and its only endomorphisms are the scalars, then `V_K`
  is simple.
- (c) If `V` is semisimple and `K` is a separable algebraic extension of `k`,
  or the endomorphism algebra of `V` is semisimple with étale centre, then
  `V_K` is semisimple.

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G n` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these.
- `ρ.baseChange b` (from
  [`Rational.ValuedRepresentationBaseChange`](../Rational/ValuedRepresentationBaseChange.md))
  is the base change of `ρ` along `b`, followed by the canonical isomorphism
  `(GL_n)_K ≅ GL_n` over `K`. Here `b` is the morphism
  `Spec K → Spec k` induced by `algebraMap k K`, so `ρK` is a representation
  of the group scheme `(GroupScheme.baseChange b).obj G = G_K` on `Kⁿ`. By
  `pointMatrix_baseChange` (same module), the matrix of `ρK` at a point of
  `G_K` is the matrix of `ρ` at the corresponding point of `G`. So `ρK` is
  Milne's `(V, r) ⊗ k'` with `V = kⁿ`.
- `σ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `F`-algebra `A`, every point `x` of the group
  with values in `A`, every `v ∈ W` and every `F`-linear map `ℓ : A → F`,
  applying `ℓ` to the coordinates of `σ(x)v` gives a vector of `W`. Since
  `W ⊗ A` is the set of vectors of `Aⁿ` all of whose images under such `ℓ`
  lie in `W`, this says that `σ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`.
  Applying it to `x⁻¹` gives equality. So the stable subspaces are the
  subrepresentations.
- `σ.IsIrreducible` (from
  [`MatrixRepresentation.DenseRationalStability`](../MatrixRepresentation/DenseRationalStability.md))
  is `Nontrivial (n → F)` together with: every stable subspace is `⊥` or
  `⊤`. The first condition says that the representation space is nonzero.
  So `IsIrreducible` is Milne's "simple".
- `IsSemisimpleRep σ`: the set inside `sSup` is the set of simple
  subrepresentations of `σ`, the nonzero stable subspaces `W` whose only
  stable subspaces contained in `W` are `0` and `W`. (A subrepresentation of
  the representation on `W` is a stable subspace of `Fⁿ` contained in `W`.)
  So `IsSemisimpleRep σ` says that `Fⁿ` is the sum of its simple
  subrepresentations, which is Milne's Definition 4.15.
- `MatrixRepresentation.Intertwines ρ ρ C` (from
  [`Lie.RepresentationSubquotient`](../Lie/RepresentationSubquotient.md))
  says: for every commutative `k`-algebra `S` and every point `x` of `G` with
  values in `S`, the matrix `C`, viewed over `S`, commutes with `ρ(x)`. So the
  set `{C | Intertwines ρ ρ C}` is the set of endomorphisms of the
  representation, `End(V, r)` in Milne's notation. It contains `1` and is
  closed under sums, products and scalar multiples, so it is already a
  `k`-subalgebra of `Matrix n n k`, and `EndAlg`, the subalgebra it
  generates, is this set. The algebra `End(V, r)` equals `k` exactly when
  every intertwiner is a scalar matrix, which is the hypothesis of (b).
- `IsSemisimpleRing EndAlg` is Mathlib's semisimplicity of the ring
  `EndAlg` (semisimple as a left module over itself).
  `Subalgebra.center k EndAlg` is the centre of `EndAlg`, a commutative
  `k`-algebra, and `Algebra.Etale k Z` is Mathlib's étale algebra (formally
  étale and of finite presentation). The centre is finite-dimensional over
  `k`, being a subspace of `Matrix n n k`. For such algebras Mathlib's
  `Algebra.FormallyEtale.iff_exists_algEquiv_prod` says: formally étale if and
  only if isomorphic to a finite product of fields each separable over `k`.
  So `Algebra.Etale k Z` is Milne's "étale k-algebra" (see below).
- `Algebra.IsSeparable k K` is Mathlib's separability: every element of `K`
  is separable (in particular algebraic) over `k`.

The statement keeps the hypotheses `[LocallyOfFiniteType G.X.hom]` and
`[IsAffineHom G.X.hom]`, so `G` is an affine algebraic group, as in Milne's
chapter 4.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

Proposition 4.19, printed pp. 90–91 (PDF pp. 106–107): "Let (V, r) be a
finite-dimensional representation of an algebraic group G over k. Let k' be
an extension of k, and let (V', r') be the representation (V, r) ⊗ k' of
G_{k'}.

(a) If (V', r') is simple (resp. semisimple), then so also is (V, r).
(b) If (V, r) is simple and End(V, r) = k, then (V', r') is simple.
(c) If (V, r) is semisimple and k' is a separable extension of k or End(V, r)
is a separable algebra over k (i.e., semisimple with étale centre), then
(V', r') is semisimple."

The surrounding conventions are:

- Affine groups. Chapter 4 opens, printed p. 83 (PDF p. 99), with
  "Throughout this chapter, G is an affine algebraic group over a field k."
  An algebraic group is "a group object in the category of algebraic schemes
  over k" (printed p. 6, PDF p. 22), and an algebraic scheme over `k` is "a
  scheme of finite type over k" (printed p. 3, PDF p. 19). The Lean statement
  therefore assumes that `G` is affine and locally of finite type (hence of
  finite type, since an affine morphism is quasi-compact).
- Extensions. Printed p. 3 (PDF p. 19): "An extension of k is a field
  containing k, and a separable extension is a separable algebraic
  extension." So "k' is a separable extension of k" in (c) is
  `Algebra.IsSeparable k K`. The same page: "Noncommutative algebras are
  referred to as "algebras over k" rather than "k-algebras"."
- Subrepresentations. The proof of Corollary 4.8, printed p. 86 (PDF p. 102):
  "A subspace W of V is stable under G if and only if it is an
  O(G)-subcomodule of V". These subspaces are the subrepresentations.
- Simple and semisimple. Definition 4.15, printed p. 90 (PDF p. 106): "A
  representation of an algebraic group is simple if it is ≠ 0 and its only
  subrepresentations are 0 and itself. It is semisimple if it is a sum of
  simple subrepresentations."
- Endomorphisms. Remark 4.18, printed p. 90 (PDF p. 106): "By an
  endomorphism of (V, r) we mean a k-linear map α: V → V such that
  α_R: V_R → V_R commutes with the action of G(R) on V_R for all small
  k-algebras R. Equivalently, it is an endomorphism of the corresponding
  comodule." This is `Intertwines ρ ρ`. The same remark says that if `(V, r)`
  is semisimple then `End(V, r)` is semisimple; so in (c) the condition on
  `End(V, r)` amounts to its centre being étale. The Lean statement keeps
  Milne's wording "semisimple with étale centre" as the conjunction
  `IsSemisimpleRing EndAlg ∧ Algebra.Etale k (Subalgebra.center k EndAlg)`.
- Separable algebras. Definition 24.27, printed p. 520 (PDF p. 536): "An
  algebra over k is separable if it is semisimple and its centre is an étale
  k-algebra." Printed p. 14 (PDF p. 30): "An étale k-algebra is a finite
  product of finite separable field extensions of k." By the Mathlib result
  cited above, for the finite-dimensional centre this is
  `Algebra.Etale k (Subalgebra.center k EndAlg)`.

The provenance is derived for these reasons:

- Milne's representation `(V, r)` is given in coordinates, as a homomorphism
  `G ⟶ GL_n` on `kⁿ` with the standard basis; every finite-dimensional
  representation is isomorphic to such a one, and all conditions in the
  statement are invariant under isomorphism.
- The three parts are combined into one conjunction in Milne's order, and the
  "resp." in (a) becomes a conjunction of two implications.
- `End(V, r)` is the set of intertwining matrices; `EndAlg` is the
  subalgebra it generates, which is the same set (see above).
- `k`, `K` and `G` lie in one universe `u`, and the test algebras in
  `IsStableSubspace` and `Intertwines` lie in the same universe. This is a
  formalization convention. The coordinate ring of `G` (resp. `G_K`) is one of
  these test algebras, so stability is the subcomodule condition and the
  intertwiners are the comodule endomorphisms.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists for
Chapter 1 a note on Notation 3.2 and corrections on pp. 18, 20, 21 and 26; for
Chapter 4 only a correction on p. 95 (proof of 4.29); for Chapter 24
corrections on pp. 513, 515, 516, 518, 524, 531 and 540, none on p. 520. None
changes the conventions of pp. 3, 6, 14 and 83 or Corollary 4.8,
Definitions 4.15 and 24.27, Remark 4.18 or Proposition 4.19. The 2022
corrected reprint (`milne-2022-algebraic-groups`, printed pp. 90–91) prints
Proposition 4.19 with the same statement, and its errata snapshot of
2026-11-04 (`milne-2022-algebraic-groups-errata-2026-11-04`) has no entry for
pp. 90–91 (its Chapter 4 entry concerns the proof of 4.14 on p. 89).

## For the proof (in `SemisimpleRepresentationFieldExtensionProof`, not part of this module)

Milne's proof, printed p. 91 (PDF p. 107): "The proof is similar to that for
representations of algebras (Bourbaki 1958, Chap. 8, §13, no. 4).
Alternatively, when k is perfect, it can be deduced from the similar
statement for algebras by using the correspondence between representations of
G and its algebra of distributions (Section l of Chapter 10)." The 2022
reprint adds "and G is connected" to the alternative. Bourbaki's Algebra,
Chapter 8, is not in the project literature. The following route reduces the
statement to finite-dimensional algebras; it is not in Milne.

Let `B ⊆ Matrix n n k` be the set of matrices `(ℓ(a_ij))`, where `(a_ij)` is
the matrix of `ρ` at the universal point (entries in the coordinate ring
`O(G)`) and `ℓ` runs over the `k`-linear maps `O(G) → k`. The counit and the
formula `Δ(a_ij) = Σ_l a_il ⊗ a_lj` show that `B` is a `k`-subalgebra.

1. A subspace of `kⁿ` is stable if and only if it is a `B`-submodule: every
   point `x` with values in `A` comes from a `k`-algebra map `φ: O(G) → A`,
   and `ℓ ∘ φ` is a linear map `O(G) → k`. A matrix `C` intertwines `ρ` with
   itself if and only if it commutes with every element of `B`, because the
   linear maps `O(G) → k` separate the elements of `O(G)`. So
   `End(V, r)` is the commutant `B'` of `B`.
2. The coefficients of `ρK` are the `a_ij ⊗ 1` in `O(G) ⊗ K`, and the
   `a_ij` span a finite-dimensional subspace of `O(G)`. Hence the algebra
   `B_K` built in the same way from `ρK` is the `K`-span of `B` in
   `Matrix n n K`, which is `B ⊗ K`.
3. (a) A `B`-submodule `W` of `kⁿ` gives the `B_K`-submodule `W ⊗ K`, which
   is `0` or `Kⁿ` only if `W` is `0` or `kⁿ`. For semisimplicity, let `W` be
   a `B`-submodule. `W ⊗ K` has a `B_K`-stable complement, hence a
   `B_K`-linear projection `p'` onto it. The `B`-linear maps `kⁿ → W` form a
   subspace `P` of `Hom_k(kⁿ, W)` cut out by linear equations over `k`, so
   the `B_K`-linear maps are `P ⊗ K`. Choose a `k`-linear `λ : K → k` with
   `λ(1) = 1` and apply `id ⊗ λ` to `p'`; the result `p ∈ P` restricts to the
   identity on `W` because `p'` does. Its kernel is a stable complement of
   `W`. A finite-dimensional representation in which every subrepresentation
   has a complement is semisimple (Milne, p. 90, citing Jacobson 1989,
   Theorem 3.10).
4. (b) `kⁿ` is a simple faithful `B`-module with `B' = k`. By the Jacobson
   density theorem, `B = Matrix n n k`. Hence `B_K = Matrix n n K`, and `Kⁿ`
   is simple.
5. (c) `kⁿ` is a faithful semisimple `B`-module, so `B` is semisimple (its
   radical annihilates every simple module). By the double centralizer
   theorem, `B = End_{B'}(kⁿ)`, so the centre of `B` is `B ∩ B'`, the centre
   `Z` of `B'`. If `Z` is étale, or if `K` is separable algebraic over `k`,
   then `Z ⊗ K` is reduced, and then `B ⊗ K` is semisimple: writing
   `B = ∏ M_{n_i}(D_i)` with `Z_i` the centre of `D_i`, each
   `D_i ⊗_k K = D_i ⊗_{Z_i} (Z_i ⊗_k K)` is a product of central simple
   algebras over the field factors of the reduced finite `K`-algebra
   `Z_i ⊗_k K`. So `Kⁿ` is a semisimple `B_K`-module, that is, `ρK` is
   semisimple.

Library material that may help: `pointMatrix_baseChange` (in
[`Rational.ValuedRepresentationBaseChange`](../Rational/ValuedRepresentationBaseChange.md));
`IsStableSubspace.isStableCoordinates` (in
[`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
and `restrictCoordinates` (in
[`MatrixRepresentation.InvariantCoordinates`](../MatrixRepresentation/InvariantCoordinates.md));
Mathlib's `IsSemisimpleModule`, `IsSemisimpleRing`, `jacobson_density`
(in `Mathlib.RingTheory.SimpleModule.Basic`) and `Algebra.FormallyEtale.iff_exists_algEquiv_prod`.
