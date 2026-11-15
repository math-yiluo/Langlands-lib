# Characters of representations of a split reductive group

`Langlands.GroupScheme.SplitRepresentationCharacterStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u`, every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `[IsAffineHom G.X.hom]` and
every `p : SplitPinning G`, the following three conjuncts hold. In this file
write

```text
ch ρ lam = Module.finrank k (p.representationWeightSpace ρ lam)
```

for a representation `ρ` and `lam : characterLattice p.torus` (this notation
is used only here; the Lean statement writes the `finrank` out). Write
`s_i = p.rootDatum.reflection i` for `i : p.rootIndex`. `IsSemisimpleRep σ`
is a local `let` in the statement, with the dimension `n` implicit:

```text
sSup {W : Submodule k (Fin n → k) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
  ∀ U : Submodule k (Fin n → k), σ.IsStableSubspace U → U ≤ W → U = ⊥ ∨ U = W} = ⊤
```

that is, `kⁿ` is the sum of its simple subrepresentations.

1. Characters are finite and Weyl invariant. For every `n : ℕ` and
   `ρ : MatrixRepresentation G (Fin n)`, the support of `lam ↦ ch ρ lam` is
   finite, and `ch ρ (s_i lam) = ch ρ lam` for every `i` and `lam`.
2. Injectivity. For all `n m : ℕ`, `ρ : MatrixRepresentation G (Fin n)` and
   `σ : MatrixRepresentation G (Fin m)` with `IsSemisimpleRep ρ`,
   `IsSemisimpleRep σ` and `ch ρ lam = ch σ lam` for every `lam`, there is
   `C : Matrix (Fin m) (Fin n) k` with `ρ.Intertwines σ C` and
   `Function.Bijective C.mulVecLin`.
3. Surjectivity onto the invariants. For every
   `f : characterLattice p.torus →₀ ℤ` with `f (s_i lam) = f lam` for every
   `i` and `lam`, there are `n m : ℕ`, `ρ : MatrixRepresentation G (Fin n)`
   and `σ : MatrixRepresentation G (Fin m)` with
   `f lam = (ch ρ lam : ℤ) - ch σ lam` for every `lam`.

In words: the character of a finite-dimensional representation of a split
reductive group is a finitely supported Weyl-invariant function on the
character lattice; two semisimple representations with the same character
are isomorphic; and every finitely supported Weyl-invariant integer function
on the character lattice is a difference of two characters.

Every ingredient is an existing declaration, used without change:

- `SplitPinning G` (from [`Reductive.Pinning`](../Reductive/Pinning.md))
  bundles `IsConnectedReductive G`, a split maximal torus `p.torus` with its
  inclusion `p.inclusion : p.torus.toGrp ⟶ G` (`p.isSplitTorus`,
  `p.isMaximalTorus`), a finite index type `p.rootIndex`, a Mathlib
  `RootDatum` `p.rootDatum` on the character and cocharacter lattices of
  `p.torus`, a proof `p.isRootDatum : IsRootDatumOf p.inclusion p.rootDatum`,
  reducedness, a base `p.base` and trivializations of the simple-root Lie
  lines. The statement uses the torus, its inclusion and the root datum; the
  base and the Lie trivializations do not occur in it.
- `IsRootDatumOf i P` (from [`Reductive.RootDatum`](../Reductive/RootDatum.md))
  says that the pairing of `P` is `latticePairing T`, that the set of roots of
  `P` is the set `roots i` of roots of `G` with respect to the torus, and that
  every reflection `P.reflection α` is induced by a point of `G` normalizing
  the torus.
- `p.rootDatum.reflection i` is Mathlib's `RootPairing.reflection`, the map
  `x ↦ x - (coroot' i x) • root i` (`RootPairing.reflection_apply`), where
  `coroot' i x` is the pairing of `x` with `coroot i`.
- `characterLattice T` (from [`Torus.Lattice`](../Torus/Lattice.md)) is
  `T ⟶ Gm`, the group of characters of `T`, written additively.
- `p.representationWeightSpace ρ lam` (from
  [`Rational.FundamentalRepresentations`](FundamentalRepresentations.md)) is
  the character space of `ρ.restrict p.inclusion` at `lam`, that is, the
  eigenspace of the torus in `kⁿ` with character `lam`. So `ch ρ lam` is
  the multiplicity of `lam` as a weight of `ρ`.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GL_n`, a representation of `G` on `kⁿ` with its
  standard basis.
- `σ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says that `W` is a subrepresentation; the condition is checked on the
  points of `G` with values in every commutative `k`-algebra.
- `ρ.Intertwines σ C` (from
  [`Lie.RepresentationSubquotient`](../Lie/RepresentationSubquotient.md))
  says that `C · ρ(x) = σ(x) · C` for every commutative `k`-algebra `S` and
  every point `x` of `G` with values in `S`. So `C` is a homomorphism of
  representations, and with `Function.Bijective C.mulVecLin` an
  isomorphism.
- `characterLattice p.torus →₀ ℤ` is Mathlib's type of finitely supported
  functions. An element `Σ_χ a_χ e^χ` of Milne's `ℤ[X]` is determined by its
  finitely supported coefficient function `χ ↦ a_χ`, and every such function
  occurs (Mathlib's group algebra `AddMonoidAlgebra ℤ X` is a structure with
  the single field `coeff : X →₀ ℤ`, and `AddMonoidAlgebra.coeffEquiv`
  identifies it with `X →₀ ℤ`). So `f` stands for `Σ_χ f(χ) e^χ`, and the
  character `ch_G(V)` for the coefficient function `λ ↦ dim V_λ`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Theorem 22.38, printed p. 474: "The homomorphism
ch_G : K(Rep(G)) → ℤ[X] is injective with image ℤ[X]^W (elements of ℤ[X]
fixed by the action of the Weyl group)."

Its setting, printed pp. 473–474:

- Grothendieck groups, p. 473: "The Grothendieck group K(A) of A is the
  commutative group with one generator for each isomorphism class of objects
  of A, and one relation [A] − [B] + [C] for each exact sequence
  0 → A → B → C → 0. If the objects of A have finite length, then K(A) is
  generated as a ℤ-module by the elements [A] with A simple."
- Example 22.36, p. 473: "Let T be a split torus over k, and let X = X*(T).
  The group algebra of X is the free ℤ-module ℤ[X] with basis the set of
  symbols {e^χ | χ ∈ X} and with e^χ · e^χ′ = e^{χ+χ′} (cf. 12.6). The
  (formal) character of a representation (V, r) of T is
  ch(V) = Σ_{χ∈X} dim(V_χ) · e^χ."
- p. 474: "Let (G, T) be a split reductive group over k, and let X = X*(T).
  We define the character ch_G(V) of a representation (V, r) of G to be its
  character as a representation of T." After Proposition 22.37: "In
  particular, the elements [V(λ)] with λ dominant generate K(Rep(G)). The
  Weyl group W of (G, T) acts on X, and hence on ℤ[X]."

Further conventions:

- Opening of Chapter 22, printed p. 463: "Throughout, representations are
  finite-dimensional unless it is specified otherwise." The weight spaces
  `V_λ` there are the eigenspaces of `T`.
- Opening of Chapter 21, printed p. 424: "The field k is arbitrary", and
  "G is split if some maximal torus T is split, in which case we refer to the
  pair (G, T) as a split reductive group." The Weyl group `W(G, T)` is
  `N_G(T)/T` (same page).
- Theorem 21.37, printed p. 435: "The Weyl group W(G, T) of (G, T) is
  generated by the elements s_α, α ∈ Φ." Its proof, printed p. 436: "When we
  identify W(G, T) with a subgroup of Aut(X(T)), the element s_α becomes
  identified with the reflection map x ↦ x − ⟨x, α∨⟩α."
- Section 6h, printed p. 135: a connected group variety `G` is reductive if
  its geometric unipotent radical is trivial; this is
  `IsConnectedReductive G`.
- Definition 4.15, printed p. 90: "A representation of an algebraic group is
  simple if it is ≠ 0 and its only subrepresentations are 0 and itself. It
  is semisimple if it is a sum of simple subrepresentations." Proposition
  4.17 (same page): such a sum contains a direct sum decomposition, "In
  particular, V is a direct sum of simple subrepresentations".

The provenance is derived for these reasons:

- No Grothendieck group. The Lean statement does not construct `K(Rep(G))`
  or `ch_G` on it; it states Theorem 22.38 through the characters of actual
  representations. The character `ch_G(V)` is the function
  `λ ↦ dim V_λ`. Every element of `K(Rep(G))` is an integer combination of
  classes `[V(λ)]` of simple representations (p. 474). Collecting the
  positive and the negative coefficients and taking direct sums, it is
  `[V] − [V′]` with `V` and `V′` direct sums of simple representations, and
  `ch_G([V] − [V′]) = ch_G(V) − ch_G(V′)`. So the image of `ch_G` is the set
  of differences of characters, and Theorem 22.38 is the conjunction of the
  three conjuncts:
  - "image ⊆ ℤ[X]^W" is conjunct 1. That `ch_G(V)` has finite support is part
    of `ch_G(V) ∈ ℤ[X]`. By Theorem 21.37 and its proof, `W` acts on `X`
    through the group generated by the reflections `s_α` for `α ∈ Φ`. These
    are the maps `s_i`: by `p.isRootDatum`, the pairing of `p.rootDatum` is
    the pairing of characters and cocharacters and its roots are the roots
    of `(G, T)`, and Mathlib's reflection has Milne's formula. A function on
    `X` is `W`-invariant exactly when it is invariant under every `s_i`.
  - "image ⊇ ℤ[X]^W" is conjunct 3.
  - "injective" is equivalent to conjunct 2. If conjunct 2 holds and
    `ch_G(x) = 0`, write `x = [V] − [V′]` as above. `V` and `V′` are
    semisimple with equal characters, so they are isomorphic, and `x = 0`.
    Conversely, suppose `ch_G` is injective and `V`, `V′` are semisimple with
    `ch_G(V) = ch_G(V′)`. Then `[V] = [V′]`. Both are direct sums of simple
    representations (Proposition 4.17), and `K(Rep(G))` is the free abelian
    group on the isomorphism classes of simple representations (the
    Jordan–Hölder theorem; the 2022 reprint states this, see below). So every
    simple representation occurs in `V` and in `V′` with the same
    multiplicity, and `V ≅ V′`.

  That `ch_G` is additive on exact sequences, so that it is defined on
  `K(Rep(G))`, is part of Milne's definition and is not stated.
- Coordinates. Finite-dimensional representations are matrix
  representations on `kⁿ`; every finite-dimensional representation is
  isomorphic to one of these. Isomorphisms of representations preserve
  semisimplicity and map the eigenspaces of `T` onto eigenspaces with the
  same character, so they preserve characters. An isomorphism is an
  intertwining matrix whose linear map is bijective.
- Pinnings. The statement is made for the torus of a split pinning. Every
  split reductive `(G, T)` in Milne's sense carries one: for a connected
  reductive `G` and a split maximal torus `i : T.toGrp ⟶ G`,
  `SplitPinning.ofRootDatum` (in
  [`Reductive.PinningConstruction`](../Reductive/PinningConstruction.md)),
  applied to a root datum given by the theorem `rootDatumExistence` (in
  [`Reductive.RootDatumExistence`](../Reductive/RootDatumExistence.md)) and
  to the root lines given by the theorem `splitRootLieLine` (in
  [`Reductive.SplitRootLieLineProof`](../Reductive/SplitRootLieLineProof.md)),
  is a split pinning with torus `T` and inclusion `i`.
- `k`, `G`, the root index type and the test algebras in `IsStableSubspace`
  and `Intertwines` lie in one universe `u`. This is a formalization
  convention.

Relation to the Library. The reflection invariance in conjunct 1 is the
proved theorem `SplitPinning.finrank_representationWeightSpace_root_reflection`
(in [`Rational.HighestWeightRootEndpoint`](HighestWeightRootEndpoint.md)),
which is Lemma 22.15 and the sentence after it. The fundamental theorem
22.2, of which Proposition 22.37 is a restatement (p. 474), is
`SplitHighestWeightClassificationStatement` (in
[`Rational.SplitHighestWeightClassificationStatement`](SplitHighestWeightClassificationStatement.md));
its predicate `IsHighestWeight` contains the character condition of 22.37
(highest weight of multiplicity one, all other weights below it). The
Library has no statement of Theorem 22.38.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Theorem 22.38 on
printed p. 475 with the same wording. Its paragraph on Grothendieck groups,
printed p. 474, reads: "If the objects of A have finite length, then the
Jordan-Hölder theorem shows that K(A) is the free abelian group with basis
the isomorphism classes of simple objects." It calls `ch_G(V)` the formal
character (p. 475), and its proof of 22.38 begins: "That the image of ch_G
is contained in ℤ[X]^W follows from Lemma 22.15." In the reprint, Theorem
21.37 (printed p. 435) says that `W(G, T)` is canonically isomorphic to the
Weyl group `W(R)` of the root datum, and Corollary 21.38 (printed p. 436)
says that `W(G, T)` is generated by the `s_α`, `α ∈ Φ`.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 22, entries on pp. 468, 469, 473 (Example 22.35 repeats Example 22.34)
and 480; for Chapter 21, entries on pp. 440, 445, 447, 449, 456–460 and 461;
and for Chapter 4, an entry on p. 95. None changes 22.36–22.38, 21.37,
4.15 or 4.17. The errata snapshot of 2026-11-04 for the 2022 reprint (source
ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapters 21 and 22, entries on p. 440 (21.19), p. 457, p. 465 (22.8) and
p. 478 (proof of 22.42), and, for Chapter 4, an entry on p. 89 (proof of
4.14); none concerns the results used here.

## For the later proof (not part of this unit)

Conjunct 1: the support is finite because eigenspaces of the torus for
distinct characters are linearly independent; reflection invariance is the
Library theorem cited above.

Conjunct 2: by Proposition 4.17 each of `ρ`, `σ` is a direct sum of simple
stable subspaces. Each simple summand has a unique dominant highest weight
and is determined up to isomorphism by it (conjuncts 3 and 2 of
`SplitHighestWeightClassificationStatement`). Characters add over direct
sums. The characters of the `V(λ)` are linearly independent: a character of
`V(λ)` has coefficient 1 at `λ` and is supported on the `μ` with
`λ - μ ∈ p.positiveRootMonoid`. So the multiplicity of each `V(λ)` in `ρ` is
determined by `ch ρ`, and the multiplicities in `ρ` and `σ` agree.

Conjunct 3, after Milne's proof (printed pp. 474–475): the orbit sums
`x_λ = Σ_{μ ∈ W·λ} e^μ`, for `λ` dominant, form a basis of `ℤ[X]^W`, since
every `W`-orbit contains exactly one dominant character. Each
`ch_G(V(λ))` is `x_λ` plus a sum of `x_{λ_i}` with dominant `λ_i < λ`. The
set of dominant `μ ≤ λ` is finite (Milne bounds it with a `W`-invariant
scalar product), and the `ch_G(V(λ))` also form a basis of `ℤ[X]^W` (Milne
argues with Zorn's lemma; induction over these finite sets also works). Writing `f` in this basis and separating positive and negative
coefficients gives `ρ` and `σ` as direct sums of the `V(λ)`, given as
block-diagonal matrix representations. The existence of `V(λ)` over an
arbitrary field is conjunct 1 of `SplitHighestWeightClassificationStatement`.
