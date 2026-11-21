# Statement: nonvanishing of the spaces `E(λ)` of Borel-equivariant functions

Worker 75.

`Langlands.GroupScheme.SplitBorelInducedNonvanishingStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Rational.DominantHighestWeight`](DominantHighestWeight.md), for `SplitPinning.IsDominantWeight`
  and, through its imports, `SplitPinning`, `latticePairing` and `IsClosedSubgroup`.
- [`Dynamic.Basic`](../Dynamic/Basic.md), for the dynamic parabolic subgroup functor
  `Dynamic.parabolic`.
- [`HomogeneousCharacterLineBundle`](../HomogeneousCharacterLineBundle.md), for the published
  all-test predicate `HomogeneousQuotientFromEmbedding.IsRightCharacterCovariant` and, through
  [`Rational.Characters`](Characters.md), the character and restriction operations.

## Lean statement

```lean
def SplitBorelInducedNonvanishingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (ν : cocharacterLattice p.torus),
    (∀ a : p.base.support, latticePairing p.torus (p.rootDatum.root a) ν < 0) →
    ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (i : B' ⟶ G), IsClosedSubgroup i →
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ p.inclusion)).IsRepresentedBy i →
    ∀ (t : p.torus.toGrp ⟶ B'), t ≫ i = p.inclusion →
    ∀ χ : rationalCharacters B',
      (∃ f : Γ(G.X.left, ⊤), f ≠ 0 ∧
        HomogeneousQuotientFromEmbedding.IsRightCharacterCovariant i (-χ) f) ↔
      p.IsDominantWeight (rationalCharacters.equivCharacterLattice p.torus (characterRestrict t χ))
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism. Points `g : T ⟶ G.X` over a
  test scheme `T` form a group, and `g * (b ≫ i.hom.hom)` is the product of `g` with the image
  of `b` in `G`.
- `SplitPinning G` ([`Reductive.Pinning`](../Reductive/Pinning.md)): `G` is connected
  reductive; `p.torus` is a split maximal torus with inclusion `p.inclusion`; `p.rootDatum` is
  the reduced root datum of `(G, T)` on the character and cocharacter lattices (its pairing is
  `latticePairing`, by `IsRootDatumOf`); `p.base` is a base of it; `p.pinning` chooses root
  vectors, which this statement does not use.
- `latticePairing T α ν` ([`Torus.Lattice`](../Torus/Lattice.md)): the integer `⟨α, ν⟩`.
- `Dynamic.parabolic χ` ([`Dynamic.Basic`](../Dynamic/Basic.md)): the points `g` whose orbit
  `s ↦ χ(s) g χ(s)⁻¹` extends from `𝔾_m` to `𝔸¹`, that is, `P(χ)`.
- `F.IsRepresentedBy i` ([`SubgroupFunctor`](../SubgroupFunctor.md)): `i` is a monomorphism and
  `SubgroupFunctor.range i = F`. `IsClosedSubgroup i`: `i` is a closed immersion.
- `rationalCharacters B'` is the additive group of group-scheme homomorphisms `B' ⟶ 𝔾_m`.
  `characterRestrict t χ` is `χ ∘ t`. The equivalence `rationalCharacters.equivCharacterLattice`
  views that restriction `λ = χ|_T` in `X(T) = Hom(T, 𝔾_m)`.
- `Γ(G.X.left, ⊤)` is the coordinate ring `O(G)`. A point `g` over a test scheme `V` evaluates
  `f` at `g.left.appTop f ∈ Γ(V, 𝒪_V)`.
- `HomogeneousQuotientFromEmbedding.IsRightCharacterCovariant i (-χ) f` imposes
  `f(gb) = (-χ)(b) f(g)` for all test schemes and their points. Here `(-χ)(b) = χ(b)⁻¹`
  by [`characterEval_neg`](../HomogeneousCharacterCoordinates.md) and
  `characterEval_apply`, so this is Milne's equation (multiplication in `Γ(V, 𝒪_V)` is
  commutative). No homogeneous quotient or line bundle is an input to this predicate.
- `p.IsDominantWeight λ` ([`Rational.DominantHighestWeight`](DominantHighestWeight.md)):
  `⟨λ, α^∨⟩ ≥ 0` for every simple root `α` of `p.base`.

## Statement and quantifiers

For every field `k : Type u`, every split pinning `p` of a group `G` over `Spec k` (so `G` is
connected reductive with split maximal torus `T`), every cocharacter `ν` of `T` with
`⟨α, ν⟩ < 0` for every simple root `α`, every closed subgroup `i : B' ⟶ G` representing
`P(ν)`, every factorization `t` of `T` through `B'`, and every character `χ` of `B'` with
restriction `λ = χ ∘ t` to `T`: there is a nonzero `f ∈ O(G)` with
`f(g b) = f(g) χ(b)⁻¹` for all points `g` of `G` and `b` of `B'` over every scheme over `k`
if and only if `λ` is dominant. In Milne's notation: `E(λ) ≠ 0` if and only if `λ` is
dominant.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*,
2022 corrected reprint, source ID `milne-2022-algebraic-groups`, file `J. S. Milne - Algebraic
Groups- The Theory of Group Schemes of Finite Type over a Field (2022 corrected reprint).pdf`.
Page numbers are printed page numbers; the PDF page is the printed page plus 11.

- Section 22a, p.464: "Let (G, T) be a split reductive group over k ... we fix a Borel
  subgroup B of G containing T. Let Φ⁺ denote the corresponding system of positive roots and
  Δ the set of simple roots in Φ⁺."
- Definition 22.1, p.464: "An element λ of X is said to be dominant if ⟨λ, α^∨⟩ ≥ 0 for all
  α ∈ Φ⁺ (equivalently, for all α ∈ Δ)."
- After Theorem 22.20, p.469: "We let B' = B⁻."
- Definition 22.21, p.469: "Let λ ∈ X(T). Regard λ as a character of B', and define E(λ) to
  be the k-subspace of O(G) of f satisfying f(gb) = f(g)λ(b⁻¹), all g ∈ G, b ∈ B'."
  Footnote 1: "More precisely, regarding f as a morphism G → 𝔸¹, we require that
  f(gb) = f(g)λ(b⁻¹) for all k-algebras R and g ∈ G(R), b ∈ B'(R)."
- Proposition 22.27(a), p.471: "Let λ ∈ X. (a) E(λ) ≠ 0 if and only if λ is dominant."

The 2017 printing (source ID `milne-2017-algebraic-groups`, file `Milne--Algebraic groups, the
theory of group schemes of finite type over a field (book)--2017.pdf`, PDF page = printed page
plus 16) defines `E(λ)` with `B` instead of `B'` (Definition 22.21, p.468: "For a character λ
of B, let E(λ) denote the k-subspace of O(G) of f satisfying f(xb) = f(x)λ(b)⁻¹") and states
Proposition 22.27(a), p.470, as "The space E(λ) is nonzero if and only if w₀(λ) is dominant."
The official errata snapshot of 2026-11-02 for the 2017 printing (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) records the change, p.468: "Redefined E(λ) to
be induced from the opposite Borel subgroup B' so as to agree with the literature. Now it is
nonzero if and only if λ is dominant etc." This statement follows the reprint. The errata
snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`) has no entry for reprint pp.464, 469 or 471.

Milne's proof in the reprint, as explanation only: if `E(λ) ≠ 0`, it contains a primitive
element of weight `λ` (22.22), so `λ` is dominant (22.17). Conversely, if `λ` is dominant, so
is `−w₀(λ)`; there is a simple representation with highest weight `−w₀(λ)` (22.20), and its
contragredient embeds into `E(λ)` (proof of 22.26).

## Derivation from the source

- **Split reductive group with `B ⊇ T`.** A split pinning `p` supplies the connected reductive
  group, the split maximal torus `T`, its reduced root datum and a base `Δ = p.base`. The
  positive system `Φ⁺` is the one with base `Δ`, and `B` is the Borel subgroup containing `T`
  with roots `Φ⁺`. Every base of the root datum of a split reductive group carries a pinning
  (root vectors for the simple roots), so quantifying over pinnings covers every pair
  `T ⊆ B`.
- **`B' = B⁻`.** The opposite Borel subgroup has roots `Φ⁻ = −Φ⁺`. For a cocharacter `ν` with
  `⟨α, ν⟩ < 0` for every simple root, `⟨α, ν⟩ < 0` for every `α ∈ Φ⁺`, so the roots of the
  dynamic parabolic `P(ν)` (the roots `α` with `⟨α, ν⟩ ≥ 0`) are exactly `Φ⁻`, and `P(ν)` is
  `B⁻`. Such `ν` exist, for example the negative of the sum of the positive coroots. The
  statement takes `B'` as a given closed representative of `P(ν)` and does not assert that one
  exists.
- **λ as a character of `B'`.** Milne regards `λ ∈ X(T)` as a character of `B'` through
  `B' → B'/B'_u ≅ T`. The statement quantifies over `χ : rationalCharacters B'` and uses
  `characterRestrict t χ` for `λ = χ ∘ t`. This is equivalent: `B'_u` is unipotent and has no
  nontrivial characters, so every character of `B' = B'_u ⋊ T` is the extension of its
  restriction to `T`.
- **`E(λ) ≠ 0`.** A nonzero `f ∈ O(G) = Γ(G, 𝒪_G)` satisfying `f(gb) = f(g)χ(b)⁻¹` for all
  points over every scheme over `k`, encoded by `IsRightCharacterCovariant i (-χ) f`.
  Testing on all schemes over `Spec k` rather than on the affine tests of footnote 1 is
  equivalent, since the condition is an equality of global sections that is local on the
  test scheme.
- **Dominant.** Definition 22.1, in its simple-root form, is `p.IsDominantWeight`.

## Related Library results

- [`SplitHighestWeightClassificationStatement`](SplitHighestWeightClassificationStatement.md)
  states the classification of simple representations by highest weight (Milne 22.2, 22.3,
  22.19).
- [`SplitDominantHighestWeightRepresentationsExistStatement`](DominantHighestWeight.md) states
  that every dominant character is the highest weight of a simple representation over an
  algebraically closed field (Milne 22.20).
- [`RegularCocharacterBorelStatement`](../Absolute/BorelStatement.md) states that `P(ν)` is a
  Borel subgroup for regular `ν`.
