# Semisimplicity through complements of codimension one

`Langlands.GroupScheme.SemisimpleRepresentationCodimensionOneStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`, if

```text
Subsingleton (G ⟶ (Gm (Spec (CommRingCat.of k))).toGrp)
```

then the following three propositions are equivalent (`List.TFAE`):

- (a) for every `n : ℕ` and every `ρ : MatrixRepresentation G (Fin n)`,
  `sSup {W | IsSimpleStable ρ W} = ⊤`;
- (b) for every `n`, `ρ` and `W : Submodule k (Fin n → k)` with
  `ρ.IsStableSubspace W` and `Module.finrank k W + 1 = n`,
  `HasStableComplement ρ W`;
- (c) for every `n`, `ρ` and `W` with `IsSimpleStable ρ W` and
  `Module.finrank k W + 1 = n`, `HasStableComplement ρ W`.

Here `IsSimpleStable` and `HasStableComplement` are local abbreviations inside
the statement, both with an implicit `n : ℕ`:

```text
IsSimpleStable ρ W :=
  ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W

HasStableComplement ρ W :=
  ∃ W' : Submodule k (Fin n → k), ρ.IsStableSubspace W' ∧ IsCompl W W'
```

In words: let `G` be an affine algebraic group over `k` without nontrivial
characters. Then every finite-dimensional representation of `G` is
semisimple if and only if every subrepresentation of codimension one of a
finite-dimensional representation has a complementary subrepresentation, if
and only if the same holds for every simple subrepresentation of codimension
one.

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these, and the three conditions are invariant under
  isomorphism.
- `Gm (Spec (CommRingCat.of k))` (from
  [`Multiplicative`](../Multiplicative.md)) is the multiplicative group
  `𝔾_m` over `k`; `.toGrp` views it as a group scheme. A morphism
  `G ⟶ (Gm _).toGrp` is a homomorphism of group schemes `G → 𝔾_m` over `k`,
  that is, a character of `G`. The constant homomorphism to the identity is
  always one, so `Subsingleton` of this type says that the trivial character
  is the only one: `X(G) = 0`.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `k`-algebra `A`, every point `x` of `G` with
  values in `A`, every `v ∈ W` and every `k`-linear map `ℓ : A → k`, applying
  `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is
  the set of vectors of `Aⁿ` all of whose images under such `ℓ` lie in `W`,
  this says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to
  `x⁻¹` gives equality. So the stable subspaces are the subrepresentations
  (`G`-submodules).
- `IsSimpleStable ρ W` says that `W` is a simple subrepresentation: it is
  nonzero and its only subrepresentations are `0` and `W`. Condition (a)
  says that `kⁿ` is the sum of its simple subrepresentations, that is, `ρ`
  is semisimple. This is the encoding of semisimplicity used in the Library's
  `SemisimpleRepresentationUnipotentStatement` (Milne 19.16 and 19.17) and
  `CharZeroReductiveSemisimpleRepresentationStatement` (Milne 22.42). For
  `n = 0` it holds trivially.
- `HasStableComplement ρ W` says that `kⁿ = W ⊕ W'` for a subrepresentation
  `W'`, which is Milne's "V = W ⊕ W' (direct sum of G-modules)"; `IsCompl` is
  the lattice complement in `Submodule k (Fin n → k)`, i.e. an internal
  direct sum of vector spaces.
- `Module.finrank k W + 1 = n` says that `W` has codimension one in `kⁿ`.

`G` is assumed affine and locally of finite type; an affine morphism is
quasi-compact, so `G` is of finite type over `k`. Together these say that `G`
is an affine algebraic group in Milne's sense.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Lemma 22.40 on printed p. 476 (PDF p. 492): "Let G be an
algebraic group over k such that X(G) = 0. The following conditions on G are
equivalent. (a) Every finite-dimensional G-module is semisimple. (b) Every
submodule W of codimension 1 in a finite-dimensional G-module V is a direct
summand: V = W ⊕ W′ (direct sum of G-modules). (c) Every simple submodule W
of codimension 1 in a finite-dimensional G-module V is a direct summand:
V = W ⊕ W′ (direct sum of G-modules)." Its proof runs from p. 476 to p. 477.
The 2022 corrected reprint (in the project literature folder, registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`) has the
same statement and proof on its printed pp. 477–478.

The surrounding conventions are:

- Algebraic groups. "An algebraic group over k is a group object in the
  category of algebraic schemes over k", and "an algebraic k-scheme is a
  scheme of finite type over k" (printed p. 6). The notation section, printed
  p. 4, says "After p. 162, all algebraic groups are affine", and printed
  p. 162 says "By "algebraic group" we shall mean "affine algebraic group"".
  Chapter 22 lies after p. 162, so `G` is an affine algebraic group, which
  the Lean hypotheses express.
- Characters. Printed p. 92: "A character of an algebraic group G over k is a
  homomorphism G → G_m." Printed p. 230: "the set of characters is a
  commutative group, denoted X(G)." So `X(G) = 0` says that the trivial
  character is the only character, which is the `Subsingleton` hypothesis.
- G-modules. Printed p. 83 (Chapter 4, where "G is an affine algebraic group
  over a field k"): a representation of `G` on `V` is the same as an action
  of `G` on the functor `V_a` through `R`-linear maps, and "When viewed in
  this way, we call (V, r) a G-module." A submodule of a `G`-module is a
  subrepresentation, which is `IsStableSubspace`.
- Simple and semisimple. Definition 4.15, printed p. 90: "A representation of
  an algebraic group is simple if it is ≠ 0 and its only subrepresentations
  are 0 and itself. It is semisimple if it is a sum of simple
  subrepresentations." This is `IsSimpleStable` and condition (a).

The provenance is derived for these reasons:

- The characteristic. Section 22c, which contains the lemma, begins on
  printed p. 475 with "In this section, k is a field of characteristic
  zero." The Lean statement does not assume characteristic zero, so it is
  stronger than the statement in its source context. Neither the statement
  of Lemma 22.40 nor its proof uses the characteristic: the proof (see the
  last section) uses only linear algebra in finite-dimensional
  representations, quotient representations, the representation on
  `Hom_k(V, W)` and the hypothesis `X(G) = 0`. It does not use the Casimir
  operator or the Lie algebra material of the section.
- Finite-dimensional `G`-modules are given in coordinates as matrix
  representations on `kⁿ`. Every finite-dimensional representation is
  isomorphic to one of these, and simplicity, semisimplicity, codimension and
  the existence of complementary subrepresentations are preserved by
  isomorphisms, so each of (a), (b), (c) is equivalent to its Lean
  counterpart.
- Milne's three conditions are combined into one `List.TFAE` proposition,
  under the common hypothesis `X(G) = 0`.
- `k`, `G` and the test algebras in `IsStableSubspace` lie in one universe
  `u`. This is a formalization convention.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 22, only corrections on pp. 468, 469, 473 and 480 (an entry for
Chapter 23, p. 506, changes a cross-reference "p.475" to "p.476" in the proof
of Lemma 23.68 and does not concern Lemma 22.40); for Chapter 4, only
a correction on p. 95 (proof of 4.29); for Chapter 12, only pp. 244 (12.41)
and 249 (12.57); for Chapter 1, a note that Notation 3.2 should be placed
earlier and corrections on pp. 18, 20, 21 and 26; under the heading Chapter 3,
corrections on p. 80 (3.52) and p. 85. None changes Lemma 22.40, Definition
4.15, Proposition 4.17 or the conventions of pp. 4, 6, 83, 92, 162 and 230.
The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 22, entries on p. 465 (22.8) and p. 478 (proof of 22.42) only; the
latter concerns Theorem 22.42, not Lemma 22.40.

## For the later proof (not part of this unit)

Milne's proof, printed pp. 476–477, with the details it leaves implicit:

- (a) ⇒ (b) ⇒ (c). Milne: "The implications (a)⇒(b)⇒(c) are trivial." For
  (a) ⇒ (b), Proposition 4.17 (printed p. 90) says that every
  subrepresentation of a sum of simple subrepresentations is a direct
  summand. (b) ⇒ (c) is a specialization.
- (c) ⇒ (b), by induction on `dim V`. Let `W ⊆ V` be a subrepresentation of
  codimension one. If `W = 0`, then `V` is a complement. If `W` is simple,
  (c) applies. Otherwise `W` has a nonzero proper subrepresentation; a
  maximal proper subrepresentation `W'` of `W` containing it is nonzero and
  `W/W'` is simple. `W/W'` is a simple subrepresentation of codimension one
  of `V/W'`, so by (c) `V/W' = W/W' ⊕ V'/W'` for a subrepresentation `V'` of
  `V` containing `W'`. Then `dim V'/W' = dim V/W = 1`, so `W'` has
  codimension one in `V'`, and `dim V' = dim W' + 1 < dim V`. By induction
  `V' = W' ⊕ L` with `L` a subrepresentation of dimension one. Since
  `V' ∩ W = W'`, `L ∩ W ⊆ L ∩ W' = 0`, so `L` is a complement of `W`.
- (b) ⇒ (a). Let `W` be a subrepresentation of `V`; if `W = 0` it is a
  direct summand, so let `W ≠ 0`. `G` acts on `Hom_k(V, W)` by
  `(gf)(v) = g·f(g⁻¹v)`. The subspaces `V₁ = {f | f|_W = a·id_W, a ∈ k}` and
  `W₁ = {f | f|_W = 0}` are subrepresentations, and `V₁/W₁` has dimension one
  because `W ≠ 0`. By (b), `V₁ = W₁ ⊕ L` with `L = ⟨f⟩` of dimension one.
  `G` acts on a one-dimensional representation through a character (printed
  p. 92), which is trivial because `X(G) = 0`; so `f` is a homomorphism of
  representations `V → W`, with `f|_W = a·id_W` and `a ≠ 0` since `f ∉ W₁`.
  Its kernel is a complementary subrepresentation of `W`. Finally, if every
  subrepresentation of every finite-dimensional `V` is a direct summand,
  then `V` is a sum of simple subrepresentations: by induction on `dim V`,
  write `V = S ⊕ C` with `S` a minimal nonzero subrepresentation (simple)
  and `C` a subrepresentation; every subrepresentation `U` of `C` with
  complement `U'` in `V` has complement `U' ∩ C` in `C`, so `C` is a sum of
  simple subrepresentations.

In the Lean setting, `V₁`, `W₁`, `V/W'` and `V'` must be given coordinates,
so that (b) and (c) apply to matrix representations on `kᵐ`; the
one-dimensional representation `L` is a homomorphism `G → GL_1`, which
`X(G) = 0` forces to be trivial after composing with the isomorphism
`GL_1 ≅ 𝔾_m`.
