# Existence statements for the absolute global Weil group

Worker 12 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. Worker 8 (task `6c50b2fd`), who built the
absolute Weil group, handed these targets to Task 12. All declarations lie in the
namespace `Langlands.ClassField.Global` and are proposition definitions. Nothing is
proved or assumed here.

The statements concern these published objects:

- `RelativeWeilGroup.IsWeilMap c F K L h φ` (module `RelativeWeilMap`): Weil maps
  `W_{L/F} → W_{K/F}`;
- `WeilMapSystem c F Ω h`, its projective limit `S.WeilGroup` and the projections
  `S.toLevel K : S.WeilGroup →ₜ* W_{K/F}` (module `AbsoluteWeilGroup`);
- `S.IsLocalWeilMap v θ` for `θ : W_{F_v} →ₜ* S.WeilGroup` at a finite place `v`
  (module `AbsoluteLocalWeilMap`);
- `RelativeWeilGroup.IsLocalRelativeWeilMap v w e ι` (module `LocalRelativeWeilMap`);
- `S.inflate K B`, the inflation along `S.toLevel K` of a representation `B` of
  `W_{K/F}` (module `Langlands.Automorphic.Unramified.AbsoluteWeilAssociation`).

The Markdown of those modules explains their conventions. Those modules prove no
existence results and list them as obligations. This module states them.

## Common hypotheses

Every statement quantifies over a class family `c : FundamentalClass.ClassFamily.{u}`
with `RelativeWeilGroup.IsArithmeticClassFamily c`. That published predicate (module
`Langlands.Automorphic.AssociatedFactorStatement`) says that, for some family `I` of
local invariant maps forming relative class formations with the arithmetic
normalization, `c` satisfies `Generates`, `Restriction`, `Inflation` and
`LocalCompatibility I`. These are the conclusions of the published
`GlobalFundamentalClassStatement`, so `c F E` is the arithmetic fundamental class and
`W_{E/F} = RelativeWeilGroup c F E` is the Weil group of the sources. The same
hypothesis is used by the published Weil-side statements of Task 12, such as
`WeakInductionAssociationStatement`.

Every statement also quantifies over `h : FundamentalClass.Restriction c`. The published
constructions take `h` as an argument. It is a proof of a proposition that already
follows from `IsArithmeticClassFamily c`, so this binder adds no hypothesis.

Number fields `F`, `K`, `L` and the field `Ω` with `[Algebra F Ω]` lie in the single
universe `u` of the published relative Weil groups. Representations have carriers in an
independent universe `uV`. The topology on `W_{K/F}` used for continuity of
representations is the global instance, as in `AbsoluteWeilAssociation`, so
`isContinuous_inflate` and `isIrreducible_inflate` apply directly.

**The layers of an arbitrary `Ω`.** The field `Ω` is arbitrary, as in the published
`AbsoluteWeilGroup`. Everything depends only on its finite Galois layers
`K : FiniteGaloisIntermediateField F Ω`. Write `Ω₁ ⊆ Ω` for their union, the maximal
subextension of `Ω` that is algebraic and Galois over `F`. Its Galois group
`Gal(Ω₁/F)` is the projective limit of the `Gal(K/F)`. This is the group of Mathlib's
`ProfiniteGrp.limit (InfiniteGalois.asProfiniteGaloisGroupFunctor F Ω)`, the target of the
published `S.toGaloisLimit`. When `Ω/F` is not normal, `Ω₁ ≠ Ω` in general, and
automorphisms of `Ω` need not induce all of `Gal(Ω₁/F)`. Example: for `Ω = ℚ(2^{1/4}) ⊂ ℝ`,
every automorphism fixes the layer `ℚ(√2)`. So no argument below uses automorphisms of
`Ω`; only `Gal(Ω₁/F)` and the layers appear. When `Ω` is an algebraic closure of `F`,
`Ω₁ = Ω`, and the limit of a system of Weil maps is Tate's absolute Weil group `W_F`.

## Statements

### `WeilMapExistenceStatement`

For every tower `F ⊆ K ⊆ L` of number fields with `[IsScalarTower F K L]`,
`[IsGalois F K]` and `[IsGalois F L]`, there is `φ` with
`RelativeWeilGroup.IsWeilMap c F K L h φ`.

Source: Artin–Tate XV, printed p.177: "According to Theorem 2, a Weil map `ϕ_{L/K}`
exists for each layer `L/K`". In the source the base field is `k` and the layers are
`L ⊃ K ⊃ k`; here they are `F ⊆ K ⊆ L`. The argument combines three results.

- Theorem 1 (printed pp.168–169): the extension of `Gal(L/F)` by `C_L` with the fundamental
  class is a Weil group of the layer `L/F`. Its maps `f_E` are inverse to the transfer.
  In the library this is the published `relativeWeilTransferReciprocity` for
  fundamental-class families.
- Theorem 3 (printed p.171): `U^L/(U^L_K)^c` is then a Weil group of `K/F`. Here
  `(U^L_K)^c` is the published `levelCommutatorClosure c F K L`.
- Theorem 2 (printed pp.170–171): any two Weil groups of `K/F` are related by a Weil
  isomorphism.

Composing the quotient map with a Weil isomorphism onto `W_{K/F}` gives a Weil map in
the sense of printed p.177. Such a map satisfies the four fields of `IsWeilMap`.
`RelativeWeilMap.md` explains why: fields 2 and 3 are WI 1 and WI 2 at `E = K`, and
fields 1 and 4 say that the map is onto with kernel `(U^L_K)^c`. The hypothesis
`IsArithmeticClassFamily c` is what makes `W_{L/F}` and `W_{K/F}` Weil groups in the
sense of Definition 1.

### `WeilMapSystemExistenceStatement`

For every number field `F`, every field `Ω` with `[Algebra F Ω]` and every `h`,
`Nonempty (WeilMapSystem c F Ω h)`.

Source: Artin–Tate XV, lemma on printed pp.178–179: if `A_K/A_k` is compact for every
`K`, a transitive collection of Weil maps exists. For number fields, `C_K/C_F` is
compact for every finite extension `K/F`; this is hypothesis WT 2 of Theorem 7 for the
idele-class formation. The proof uses Weil maps for every pair of layers (the statement
above), the compact space `X_{L,K}` of Weil maps (printed p.178), continuity of
composition (lemma on printed p.178) and the finite intersection property.

**Derived formulation.** The source works with the normal layers of a class formation.
The layers here are Mathlib's `FiniteGaloisIntermediateField F Ω` for an arbitrary
`Ω`. These are the finite Galois extensions of `F` inside the maximal Galois
subextension of `Ω/F`, and their idele class groups form the corresponding class
formation. The lemma uses only finite sets of layers and the existence of a common
upper bound, so it applies to every `Ω`. For Tate's `W_F`, take `Ω` an algebraic
closure of `F`.

### `WeilLevelSurjectiveStatement`

For every `S : WeilMapSystem c F Ω h` and every finite Galois layer `K`,
`Function.Surjective (S.toLevel K)`.

Source: Artin–Tate XV, proof of Theorem 7, printed pp.179–180. The kernel of each Weil
map is compact: it contains `C_L ∩ ker φ_{L/K}` with finite index, and on `C_L` the map
is the norm (published `IsWeilMap.map_inclusion`). The kernel of the norm contains
`I_{G_{L/K}} C_L` with finite index, and `I_{G_{L/K}} C_L` is compact because `C_L/C_K`
is compact (WT 2). "Using the compactness of the kernels of the maps `ϕ_{M/L}` … one
shows easily that `ϕ_L` is onto" (printed p.180). The source's `ϕ_L` is `S.toLevel L`.

The published `isIrreducible_inflate` takes this surjectivity as a hypothesis.

### `LocalWeilMapExistenceStatement`

For every `S` and every finite place `v : Langlands.Global.FinitePlace F`, there is
`θ : W_{F_v} →ₜ* S.WeilGroup` with `S.IsLocalWeilMap v θ`.

Source: Tate 1979, Proposition (1.6.1), printed p.8. For an `F`-embedding
`i : \bar F → \bar{F_v}`, there is a continuous `θ_v : W_{F_v} → W_F` compatible with
`G_{F_v} → G_F` and, for each finite `E`, with `η : C_{E_v} → C_E` through the
reciprocity maps.

**Derived formulation.**

1. *The global Weil group.* By Artin–Tate's Theorem 7 (printed pp.179–181), the
   projective limit along any transitive system of Weil maps is a Weil group for the
   class formation of the layers. For `Ω` an algebraic closure this is Tate's `W_F`.
   Tate's (W4) identifies every Weil group with the projective limit of its `W_{E/F}`.
   So the statement is made for every system `S`.
2. *Level-by-level predicate.* `IsLocalWeilMap` asks, at each layer `K`, for a place
   `w` above `v`, a candidate `e` and an element `x` of `W_{K/F}`. With these,
   `toLevel K ∘ θ` followed by conjugation by `x` must be a local-to-relative Weil map.
   Tate's `θ_v`, composed with `W_F → W_{K/F}`, gives such a map at the place `w`
   induced by `i`, as explained in the Markdown of the published
   `LocalRelativeWeilMapExistenceStatement`. The element `x` absorbs the difference
   between `i|_K` and the embedding `K → K_w → \bar{F_v}` chosen in the library
   (`AbsoluteLocalWeilMap.md`, derived formulation 2).
3. *Arbitrary `Ω`.* Tate states (1.6.1) for a separable closure. His proof is
   analogous to that of (1.3.1). It builds the map as a projective limit of maps into
   the `W_{E/F}` for the finite Galois `E`, using compactness of `C_E/C_F` and the
   vanishing of `H¹(Gal(E_v/F_v), C_E)`. It involves only these layers and an embedding
   of their union. So it applies to the finite Galois layers of any `Ω/F`, with `i` an
   `F`-embedding of the algebraic extension `Ω₁` into `\bar{F_v}`. No automorphism of
   `Ω` is used.

Archimedean places are not treated, as in the published predicate.

### `LocalWeilMapConjugacyStatement`

For every `S`, every finite place `v` and all `θ θ'` with `S.IsLocalWeilMap v θ` and
`S.IsLocalWeilMap v θ'`, there is `y : S.WeilGroup` with `θ' = S.conjMap y θ`.

Source: Tate 1979, (1.6.1), printed p.8: for a fixed `i`, `θ_v` is unique up to an
inner automorphism of `W_F` by an element of `W_F^0 = Ker φ`.

**Derived formulation.** Tate's uniqueness concerns maps compatible with one fixed
embedding. `IsLocalWeilMap` instead provides, at each layer separately, a place, a
candidate and a conjugating element. The conclusion follows from Tate's result in three
steps, with `Ω₁` as in *The layers of an arbitrary `Ω`*.

1. *One embedding for each local-to-global map.* Let `S.IsLocalWeilMap v θ`. For a layer
   `K`, let `J_K` be the set of `F`-embeddings `j : K → \bar{F_v}` such that
   `toLevel K ∘ θ` satisfies conditions 2 and 3 of `IsLocalRelativeWeilMap`, with `j` in
   place of the library's embedding `K → K_w → \bar{F_v}` and with the place of `K`
   induced by `j`. Each `J_K` is finite.

   `J_K` is nonempty. If `(w, e, x)` witnesses the predicate at `K`, compose the
   library's embedding for `w` with the automorphism of `K` given by the image of `x` in
   `Gal(K/F)`. Conjugation by `x` changes the Galois image by that automorphism and moves
   `C_K` along it, so the composite embedding lies in `J_K`.

   For `K ≤ L`, restriction to `K` maps `J_L` into `J_K`. Condition 2 restricts directly,
   by field 2 of `IsWeilMap`. For condition 3, let `g` fix `j(K)`. Then
   `toLevel L (θ g)` lies in `U^L_K`, the range of the published
   `restrictionInclusion : W_{L/K} → W_{L/F}`. On `U^L_K`, the Weil map
   `W_{L/F} → W_{K/F}` is the inclusion of the transfer `W_{L/K} → C_K` (field 3 of
   `IsWeilMap`). On the subgroup of `W_{F_v}` fixing `j(K)`, which the published
   `extensionWeilMap_range` identifies with the Weil group of `K_w`, the map
   `toLevel L ∘ θ` is a local-to-relative Weil map for `L/K`. The transfer of such a map
   to `C_K` is inverse local reciprocity of `K_w` followed by `K_wˣ → C_K`. This is the
   published `LocalTransferReciprocityStatement`, Tate's (W 3) at finite level. So
   condition 3 holds at `K`.

   An inverse limit of nonempty finite sets is nonempty. Hence there is an `F`-embedding
   `i : Ω₁ → \bar{F_v}` such that `θ` is compatible with `i|_K` at every layer `K`. This is
   Tate's compatibility with an embedding, tested on the finite Galois layers, which is
   all that his uniqueness argument uses.
2. *Change of embedding.* `Ω₁/F` is normal, so two `F`-embeddings `i, i' : Ω₁ → \bar{F_v}`
   satisfy `i' = i ∘ τ` for some `τ ∈ Gal(Ω₁/F) = lim Gal(K/F)`. The projection
   `S.WeilGroup → Gal(Ω₁/F)` (the published `toGaloisLimit`) is surjective, as in Tate
   (1.4.4), printed p.6, for `Ω₁ = \bar F`. At each layer, the elements of `W_{K/F}` over
   `τ|_K` whose norm `‖·‖` is `1` form a nonempty compact set, a coset of the compact
   group `C_K^1`. Weil maps preserve projections and norms. So the projective limit of
   these sets is nonempty. If `y` lies over `τ`, conjugation by `y` turns a map compatible
   with one of `i, i'` into a map compatible with the other.
3. *Fixed embedding.* For maps compatible with the same embedding, Tate's (1.6.1) gives
   conjugacy by an element of `W_F^0 = Ker φ`. His proof (analogous to (1.3.1)) runs over
   the finite Galois layers, so it applies to `S.WeilGroup` for every `Ω`.

Hence any two local-to-global Weil maps at `v` are conjugate in `S.WeilGroup`. The
published `IsLocalWeilMap.conjMap` proves the converse: every conjugate of a
local-to-global Weil map is one. So, with the existence statement, the local-to-global
Weil maps at `v` form exactly one conjugacy class. Tate's sharper `W_F^0` form needs a
fixed embedding and is not stated.

### `LocalWeilMapLiftStatement`

For every `S`, finite place `v`, layer `K`, place `w : FinitePlacesAbove K v`, candidate
`e` and `ι : W_{F_v} →ₜ* W_{K/F}` with `IsLocalRelativeWeilMap v w.1 e ι`, there are `θ`
with `S.IsLocalWeilMap v θ` and `x : W_{K/F}` with
`S.toLevel K (θ g) = x * ι g * x⁻¹` for all `g`.

This is a derived consequence of (1.6.1). By the existence statement there is a
local-to-global `θ₀`. By the published `IsLocalWeilMap.exists_level`, at `K` the map
`toLevel K ∘ θ₀` is conjugate to a local-to-relative `ι₀` for some `w₀` and `e₀`. Two
local-to-relative Weil maps at the same level are conjugate in `W_{K/F}`:

- for the same `w` and `e`, by an element of `C_K`, through the vanishing of
  `H¹(D_w, C_K)` (published `LocalRelativeWeilMapConjugacyStatement`);
- for different places, by an element over the Galois automorphism carrying one place
  to the other. The geometric reciprocity isomorphisms of the two completions
  correspond, by the uniqueness in `LocalClassField.WeilReciprocityExistenceUniqueness`.

So `θ₀` itself works. `AbsoluteWeilAssociation.md` lists this lifting as the input
missing for the converse comparison from absolute to relative weak association.

### `WeilRepresentationFactorizationStatement`

For every `S` and every `A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup` with
`A.IsContinuous`, there are a layer `K` and
`B : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F K)` with `B.IsContinuous`
and `Nonempty (FiniteRepresentation.Equiv A (S.inflate K B))`.

Source: Tate 1979, §2.1, printed p.9: "Since `W_F = proj lim {W_{E/F}}` and `GL(V)` has no
nontrivial small subgroups, `ρ` must factor through `W_{E/F}`, for some finite Galois
extension `E` of `F`." In Tate's §2, a representation is a continuous homomorphism to
`GL(V)` with `V` finite-dimensional and complex. `A.IsContinuous` is continuity of
`A.representation` for the module topology on `End(V)`.

**Derived formulation.** "Factors through `W_{E/F}`" is stated as equivalence with an
inflation. `B` has the same carrier universe as `A`, and its continuity is part of the
conclusion. The expected proof uses the compact kernels of the projections (as in the
surjectivity statement): they shrink to the identity, so one of them lies in the
preimage of a neighbourhood of `1` in `GL(V)` containing no nontrivial subgroup. The
representation is then trivial on that kernel. Since `S.toLevel K` is surjective and
open, `A` descends to a continuous `B`.

### `AbsoluteWeilGroupStatement`

The conjunction of the seven statements above. Its universe parameters are `u` (fields
and class families) and `uV` (representation carriers, used only by the factorization
statement).

## Scope and retained gaps

- Only existence, surjectivity, conjugacy, lifting and factorization are stated.
  Several results about the projective limit `S.WeilGroup` are not stated:
  - the Weil group axioms W 1–W 4 for it, when `Ω` is an algebraic closure of `F`;
  - the surjectivity of its projection onto `Gal(Ω₁/F)` (used in the rationale of
    `LocalWeilMapConjugacyStatement`);
  - for Galois `Ω/F`, the density of the image of the published
    `toGalois : S.WeilGroup → Gal(Ω/F)`;
  - the isomorphisms `f_E`;
  - the uniqueness of `W_F` up to isomorphism (Artin–Tate Theorem 7; Tate (1.3.1)).
- Local-to-global maps are treated only at finite places, as in the published
  predicate.
- Tate's uniqueness up to `W_F^0` for a fixed embedding is replaced by conjugacy in
  `S.WeilGroup`; see `LocalWeilMapConjugacyStatement`.
- No statement is proved. Each is a separate proof obligation.

## Provenance

- E. Artin and J. Tate, *Class Field Theory*, AMS Chelsea 2009, literature ID
  `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`, PDF page =
  printed page + 9. Read from the original: Chapter XV, Definition 1 (printed p.167),
  Theorem 1 (printed pp.168–169), Definition 2 and Theorems 2–3 (printed pp.169–171), the definition of
  Weil maps and the lemmas on printed pp.177–179, and Theorem 7 with its proof (printed
  pp.179–181).
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  literature ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`, PDF page =
  printed page + 9. Read from the original: §1.1–1.2 (printed pp.3–5), (1.3.1)
  (printed pp.5–6), (1.4.4) (printed pp.6–7), (1.5.1)–(1.5.2) (printed pp.7–8),
  (1.6.1) and its Corollary (printed pp.8–9), and §2.1 (printed p.9).
