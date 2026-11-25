# Every character of a closed split torus occurs as a weight

`Langlands.GroupScheme.SplitTorusCharacterWeightStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with `[IsAffineHom G.X.hom]`,
the following two conjuncts hold.

1. Closed split tori. For every commutative group scheme
   `T : CommGroupScheme (Spec (CommRingCat.of k))`, every homomorphism
   `i : T.toGrp ⟶ G`, every proof `hT : IsSplitTorus T.toGrp` with
   `IsClosedSubgroup i`, and every `χ : rationalCharacters T.toGrp`, there
   are `n : ℕ` and `ρ : MatrixRepresentation G (Fin n)` with

   ```text
   (ρ.restrict i).characterSpace χ ≠ ⊥
   ```

   Here `letI := hT.isAffineHom` supplies the instance
   `IsAffineHom T.toGrp.X.hom` that `characterSpace` requires.
2. Split pinnings. For every `p : SplitPinning G` and every
   `lam : characterLattice p.torus`, there are `n : ℕ` and
   `ρ : MatrixRepresentation G (Fin n)` with
   `p.representationWeightSpace ρ lam ≠ ⊥`.

In words: let `T` be a split torus that is a closed subgroup of an affine
group scheme `G` over a field. Every character of `T` is a weight of `T` in
some finite-dimensional representation of `G`. In particular this holds for
the split maximal torus of a split reductive group.

Conjunct 2 is the special case of conjunct 1 for `T = p.torus` and
`i = p.inclusion`, which is a closed subgroup because `p.isMaximalTorus`
contains `IsClosedSubgroup p.inclusion`. It is stated separately so that it
can be used with the weight spaces of split pinnings.

Every ingredient is an existing declaration, used without change:

- `IsSplitTorus T.toGrp` (from [`Torus.Split`](../Torus/Split.md)) says that
  `T` is isomorphic, as a group scheme over `Spec k`, to the split torus
  `splitTorus (Spec k) I`, a product of copies of `𝔾_m` indexed by a finite
  type `I`. `hT.isAffineHom` (from
  [`Torus.SplitReductiveProof`](../Torus/SplitReductiveProof.md)) is the
  theorem that such a `T` is affine over the base.
- `IsClosedSubgroup i` (from [`Reductive.Basic`](../Reductive/Basic.md)) says
  that the underlying morphism of schemes of `i` is a closed immersion.
- `rationalCharacters T.toGrp` (from [`Rational.Characters`](Characters.md))
  is the additive group of homomorphisms `T ⟶ 𝔾_m` of group schemes over
  `Spec k`, that is, the characters of `T` over `k`.
- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. `ρ.restrict i` (same module) is the
  composite `i ≫ ρ`, the restriction of `ρ` to `T`.
- `σ.characterSpace χ` (from
  [`MatrixRepresentation.CharacterSpaces`](../MatrixRepresentation/CharacterSpaces.md))
  is the subspace of vectors `v ∈ kⁿ` with `σ(x) v = χ(x) v` at the
  universal point `x` of `T`, whose coordinate ring is `O(T)`. This is the
  coaction equation of Milne's Proposition 4.22 (quoted below) written in
  coordinates. The theorem
  `characterSpace_affine` of that module gives `σ(x) v = χ(x) v` for every
  point `x` of `T` with values in any commutative `k`-algebra. So
  `characterSpace` is the eigenspace with character `χ`, and it is nonzero
  exactly when `T` acts on some nonzero subspace through `χ`.
- `SplitPinning G` (from [`Reductive.Pinning`](../Reductive/Pinning.md))
  bundles connected reductivity of `G`, a split maximal torus `p.torus` with
  its inclusion `p.inclusion`, a reduced root datum, a base and
  trivializations of the simple-root Lie lines. Only the torus, its
  inclusion and `p.isSplitTorus` enter conjunct 2.
  `p.isMaximalTorus : IsMaximalTorus p.inclusion` (from
  [`Torus.Maximal`](../Torus/Maximal.md)) includes
  `IsClosedSubgroup p.inclusion`.
- `p.representationWeightSpace ρ lam` (from
  [`Rational.FundamentalRepresentations`](FundamentalRepresentations.md)) is
  the character space of `ρ.restrict p.inclusion` at the character that
  corresponds to `lam` under `rationalCharacters.equivCharacterLattice`
  (from [`Rational.Characters`](Characters.md)). That equivalence is the
  identity map, since both types are `T ⟶ 𝔾_m`.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

Proposition 22.13, printed p. 465: "Every character of T occurs as a weight
in some representation of G."

The setting is that of Chapter 22, printed p. 463: "Throughout,
representations are finite-dimensional unless it is specified otherwise."
And: "Let (G, T) be a split reductive group over k, and let (X, Φ, Φ∨) be
its root datum. Because T is split, every representation (V, r) of G
decomposes into a direct sum V = ⊕_{λ ∈ X(T)} V_λ of its weight spaces V_λ
for the action of T (see 12.12). The λ for which V_λ ≠ 0 are called the
weights of (V, r)." Further conventions:

- Chapter 21, printed p. 424: "The field k is arbitrary", and "G is split if
  some maximal torus T is split, in which case we refer to the pair (G, T) as
  a split reductive group". Notation, printed p. 4: "After p. 162, all
  algebraic groups are affine".
- Definition 12.14, printed p. 236: "A torus over k is split if it is
  isomorphic to a product of copies of Gm over k."
- Section 4g, printed p. 92: a character of `G` is a homomorphism
  `G → Gm`; "we say that G acts on a subspace W of V through a character χ
  if W is stable under G and G acts on W through χ", and "there is a largest
  subspace V_χ of V on which G acts through χ, called the eigenspace for G
  with character χ". Proposition 4.22 (printed p. 92):
  "V_χ = {v ∈ V | ρ(v) = v ⊗ a(χ)}", where `ρ : V → V ⊗ O(G)` is the
  coaction of the representation and `a(χ)` the group-like element of
  `O(G)` attached to `χ`. The weight space `V_λ`
  of Chapter 22 is this eigenspace for `T`.
- Section 4g, printed p. 94: "Let H be an algebraic subgroup of an
  algebraic group G and χ a character of H. We say that χ occurs in a
  representation (V, r) of G if H acts on some nonzero subspace of V
  through χ." For `H = T` this is `V_χ ≠ 0`.

So 22.13 says: for every character `χ` of `T` there is a finite-dimensional
representation `V` of `G` with `V_χ ≠ 0`, where `V_χ` is the eigenspace of
`T` acting on `V`. Conjunct 1, with `G` reductive and `T` a split maximal
torus, says exactly this.

The provenance is derived for these reasons:

- Generality. Conjunct 1 is stronger than 22.13. It applies to every affine
  group scheme `G` over `k`: `G` need not be of finite type, smooth,
  connected or reductive. And `T` is any split torus with a closed
  immersion `T → G`, not necessarily maximal. Milne's argument (below) uses
  only that `G` is affine, that `T` is a split torus and that the
  restriction map `O(G) → O(T)` is surjective, which holds because `T` is a
  closed subgroup of the affine `G`. Proposition 4.7 and Corollary 4.8,
  which the argument applies to `G`, are stated for algebraic groups, but
  their proofs (printed p. 86) do not use finite type. Closedness cannot be
  dropped: for the trivial homomorphism `𝔾_m → 1`, only the zero character
  occurs.
- Pinnings. Conjunct 2 is the same assertion for the torus of a split
  pinning, which carries data that Milne does not fix (a root datum, a base
  and Lie vectors). Every split reductive `(G, T)` in Milne's sense is
  covered by conjunct 1, whether or not a pinning is chosen.
- Coordinates. Finite-dimensional representations are given as matrix
  representations on `kⁿ`; every finite-dimensional representation is
  isomorphic to one of these, and an isomorphism of representations maps
  eigenspaces of `T` onto eigenspaces with the same character.
- `k`, `G`, `T` and the test algebras in `characterSpace_affine` lie in one
  universe `u`. This is a formalization convention.

Relation to the Library. No Library declaration states that a prescribed
character occurs as a weight. The Library's
`SplitPinning.finrank_representationWeightSpace_root_reflection` (in
[`Rational.HighestWeightRootEndpoint`](HighestWeightRootEndpoint.md)) says
that every root reflection preserves the dimensions of weight spaces, as in
Lemma 22.15 and the sentence after it; this is a different statement.

Corrected reprint. The 2022 corrected reprint (in the project literature
folder, registered as `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`; printed page
numbers, the PDF page is the printed page plus 11) has Proposition 22.13 on
printed p. 466 with the same wording. Its proof, on printed p. 467, is
different from the 2017 proof (see the last section).

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 22, corrections on pp. 468, 469 (the construction of `E(λ)` and
Lemma 22.24), p. 473 (Example 22.35) and p. 480 (Theorem 22.52); none
concerns pp. 463–466. Its Chapter 4 entry (p. 95, proof of 4.29) and
Chapter 12 entries (pp. 244, 249) do not concern 4.7, 4.8, 4.22, 4.24,
12.12 or 12.14. The errata snapshot of 2026-11-04 for the 2022 reprint
(source ID `milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has, for
Chapter 22, entries on p. 465 (22.8) and p. 478 (proof of 22.42), and, for
Chapters 4 and 12, entries on p. 89 (proof of 4.14) and p. 234 (Example
12.10); none concerns 22.13 or the results its proof uses.

## For the proof (not part of this module)

The Library proves the proposition as `splitTorusCharacterWeight` in
[`Rational.SplitTorusCharacterWeightProof`](SplitTorusCharacterWeightProof.md).

Milne's 2017 proof, printed p. 466: let `χ ∈ X(T)`. As `O(G) → O(T)` is
surjective, there is `f ∈ O(G)` with `f|T = χ`. "The action of T on O(G) is
semisimple", so `f = f₁ + ⋯ + f_r` with `f_i` an eigenfunction for `T`
with character `χ_i`, the `χ_i` distinct. (The printed text has
"f_i ∈ O(X)_{χ_i}"; `O(G)` is meant.) Evaluating at `t ∈ T(R)` gives
`χ = Σ f_i(1) χ_i`, and by linear independence of distinct characters
(Corollary 4.24, printed p. 93) `χ = χ_i` for some `i`, with
`f_i(1) = 1`, so `f_i ≠ 0`. This shows that `χ`
is a weight of `T` in the regular representation `O(G)`, which is
infinite-dimensional. To reach a finite-dimensional representation one
also needs Corollary 4.8 (printed p. 86): `f_i` lies in a
finite-dimensional subrepresentation `V` of `O(G)`, and then
`0 ≠ f_i ∈ V_χ`. The 2017 proof leaves this step implicit.

The 2022 reprint's proof, printed p. 467: "T acts on the line kχ in O(T)
through χ. As the homomorphism of coordinate rings O(G) → O(T) is
surjective, there exists a finite-dimensional G-submodule V of O(G) whose
image contains kχ. Now χ occurs as a weight of T in V." The last step
uses that the restriction map `V → O(T)` is `T`-equivariant, that `V` is the
sum of its `T`-eigenspaces (12.12, `T` split), and that the eigenspace of
`O(T)` with character `μ` is the line `kμ`.

In the Lean setting a proof must give a finite-dimensional
subrepresentation of the regular representation of `G` coordinates `kⁿ`,
as a `MatrixRepresentation G (Fin n)`, and must compare `characterSpace`
with eigenfunctions in `O(G)`. Conjunct 2 then follows from conjunct 1.
