# Statements: representability of the torus normalizer and the point quotients `N/Z`

This file states three targets about a split subtorus `i : T ⟶ G` of a connected
reductive group `G` over a field `k`. The objects come from the published module
`Langlands.GroupScheme.Rational.TorusNormalizer`:

- the all-test normalizer `torusNormalizer i`;
- the published centralizer `torusCentralizer i`;
- the point quotient `pointWeylGroup i U = N(U) ⧸ Z(U)`;
- the restriction map `relativeWeylGroupRestrict i U : relativeWeylGroup i →* pointWeylGroup i U`.

No target is proved here. Each is a `Prop`-valued definition for a later proof task.
All quotients in this file are quotients of groups of points. None of them is the
group of points of a quotient scheme `N/Z`.

Sources:

- Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`. Printed page
  numbers are PDF page numbers minus 16.
- Borel–Tits, *Groupes réductifs* (1965), source `borel-tits-1965-groupes-reductifs`.
  Printed page numbers are PDF page numbers plus 53.

## Smooth closed representatives

`SubgroupFunctor.HasSmoothClosedRepresentative F` says there are a group scheme `H`
and a homomorphism `j : H ⟶ G` such that:

- `j` is a closed subgroup (published `IsClosedSubgroup`, a closed immersion);
- the structure morphism `H.X.hom` is smooth;
- `j` represents `F` (published `IsRepresentedBy`: `j` is a monomorphism and
  `range j = F`).

The lemma `HasSmoothClosedRepresentative.hasClosedRepresentative` forgets smoothness
and gives the predicate `HasClosedRepresentative` of the definitions module.

## Target 1: `TorusNormalizerRepresentableStatement`

For every field `k`, every connected reductive `G` over `Spec k`, and every split
subtorus `i : T ⟶ G` (published `IsSplitSubtorus`: `T` is a split torus and `i` is a
closed subgroup), both `torusNormalizer i` and `torusCentralizer i` have smooth
closed representatives.

Sources:

- Milne Proposition 1.83, printed p.31 (PDF p.47): for an algebraic subgroup `H` of
  `G` there is a unique algebraic subgroup `N_G(H)` representing
  `R ⇝ {g ∈ G(R) | g H(R') g⁻¹ = H(R')` for all `R`-algebras `R'`}.
- Milne Proposition 1.92, printed p.33 (PDF p.49): the same for the centralizer
  `C_G(H)`.
- Milne Corollary 13.10, printed p.257 (PDF p.273): "Let H be a subgroup variety of a
  group variety G. If H is a multiplicative type, then C_G(H) and N_G(H) are smooth."

Here `H` is the image of `i`. It is an algebraic subgroup, since `i` is a closed
immersion. It is a subgroup variety of multiplicative type, since `T` is a split
torus. `G` is a group variety, since connected reductive groups are smooth.

The target is a derived formulation in two respects.

1. The Lean functors test every `k`-scheme mapping to `U`, not only affine ones. Both
   sides are Zariski sheaves and agree on affine test schemes, so the representing
   subgroups of Milne also represent the all-test functors.
2. The subtorus need not be maximal, because the cited results do not use
   maximality.

## Target 2: `RelativeWeylGroupRestrictStatement`

Let `i` be a maximal split torus (published `IsMaximalSplitTorus`) of a connected
reductive `G` over `k`. Let `U` be any `k`-scheme whose underlying space is
connected; Mathlib's `ConnectedSpace` includes nonemptiness. Then the restriction

`relativeWeylGroupRestrict i U : N(k)/Z(k) → N(U)/Z(U)`

is bijective. The spectrum of any field extension `K` of `k` is such a `U`, so this
includes `N(k)/Z(k) ≅ N(K)/Z(K)`. Here `N(K)` is still the normalizer of the given
torus, which need not be maximal split over `K`.

Sources:

- Milne 25.16(b)(c), printed p.549 (PDF p.565): for a maximal split torus `S`,
  "every connected component of N_G(S) meets G(k)" and "the quotient N_G(S)/C_G(S)
  is a finite constant group scheme".
- Milne 25.17, same page: "Every coset of C_G(S) in N_G(S) is represented by an
  element of N_G(S)(k)."
- Borel–Tits Théorème 5.3, printed p.96 (PDF p.43): "Chaque composante connexe de
  𝒩(S) rencontre G_k."

Derivation of the formulation. By target 1, `N(U)` and `Z(U)` are the `U`-points of
`N_G(S)` and `C_G(S)`. Let `W` be the quotient group scheme `N_G(S)/C_G(S)`. Then:

1. The kernel of `N_G(S)(U) → W(U)` is `C_G(S)(U)`, so `N(U)/Z(U)` embeds in `W(U)`.
2. `W` is finite and constant (Milne 25.16(c)), so `W(U)` is the finite group `W(k)`
   for connected nonempty `U`.
3. The composite `N(k)/Z(k) → N(U)/Z(U) → W(U) = W(k)` is the map of Milne 25.17. It
   is injective by step 1 with `U = Spec k`, and surjective because every coset has a
   rational representative.

Hence the first map is bijective.

The official Milne errata (source `milne-2017-algebraic-groups-errata-2026-11-02`,
entry for p.549) say that the statement in 25.16 that the relative root system is a
root system is correct. They also say its classical proofs (Borel–Tits 1965, Borel
1991, Springer 1998) are incomplete, and refer to Conrad–Gabber–Prasad (2015) C.2.15
for a complete proof. The entry corrects no statement used here. The errata contain
no entries for 1.83, 1.84, 1.92, 1.93 or 13.10.

Connectedness is necessary:

- For empty `U`, `N(U)/Z(U)` is trivial.
- For `U = Spec k ⊔ Spec k`, `N(U)/Z(U) = W × W` and restriction is the diagonal.

So bijectivity fails in both cases whenever `W` is nontrivial.

## Target 3: `NormalizerPointsInfiniteFieldStatement`

Let `k` be infinite and `i` a split subtorus of a connected reductive `G`. Write
`i(T(k)) = (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))` for the subgroup of
torus points in `G(k)`. Then:

- the published `normalizerPoints i` equals Mathlib's `Subgroup.normalizer` of
  `i(T(k))`;
- the published `centralizerPoints i` equals Mathlib's `Subgroup.centralizer` of
  `i(T(k))`.

Sources:

- Milne Proposition 1.84, printed p.32 (PDF p.48): "Let H be a smooth algebraic
  subgroup of G and let k' be an extension of k such that H(k') is dense in H. Then
  N_G(H)(k) consists of the elements of G(k) normalizing H(k') in G(k')."
- Milne Proposition 1.93, printed p.34 (PDF p.50): the same for `C_G(H)(k)` and
  elements centralizing `H(k')`.

These are applied with `k' = k` and `H` the image of `i`. Density holds because
`T ≅ 𝔾_m^r` and `(k^×)^r` is Zariski dense in `𝔾_m^r` when `k` is infinite: a
Laurent polynomial vanishing on `(k^×)^r` is zero. This step is elementary and not
quoted from the sources.

The published `normalizerPoints i` consists of the `n` with
`i ≫ int(n) = σ ≫ i` for some automorphism `σ` of `T`. For a closed subgroup `i`
this is `n S n⁻¹ = S` as subschemes, which is Milne's `N_G(H)(k)`. Likewise
`centralizerPoints i` is `C_G(H)(k)`.

Neither maximality nor reductivity is used by the source argument. The common
hypotheses are kept so that the three targets have the same shape.

The hypothesis that `k` is infinite cannot be dropped. Take `G = GL₂` over `𝔽₂` and
`S` the diagonal torus. Then:

- `S(𝔽₂)` is trivial;
- its abstract normalizer and centralizer are all of `GL₂(𝔽₂)`, which has order 6;
- `N_G(S)(𝔽₂)` is the group of monomial matrices, of order 2;
- `C_G(S)(𝔽₂) = S(𝔽₂)` is trivial.

## Provenance

The three targets are derived formulations of the cited results for the published
`Grp(Over (Spec k))` and `SubgroupFunctor` architecture:

- the all-test functors of target 1;
- the point quotient over a connected test scheme in target 2;
- the identification with the published `normalizerPoints` and `centralizerPoints`
  in target 3.

The derivations are given in the sections above.
