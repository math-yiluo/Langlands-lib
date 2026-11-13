# Real coroots, real bases and standard Levi decompositions

Worker 4, for Task 1222. Module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`, namespace
`Langlands.GroupScheme`.

This file states Renard V.3.7, the real form of V.3.12 and V.3.13 (in the
corrected form of source issue I4) for the minimal standard parabolic subgroup
and pairs of standard Levi subgroups. It contains five `Prop`-valued statement
definitions and the auxiliary definitions they need. It proves none of the
statements. The only theorems are three short facts about the new definitions:
`simpleRelativeRoots_subset_relativeRoots`, `pair_tmul_realCoroot` and
`pair_root_realCoroot`.

The statement targets are:

- `RelativeRealSimpleRootBasisStatement` (V.3.12, real form of the simple-root
  basis);
- `RelativeRealCorootStatement` (V.3.7 for the minimal parabolic);
- `RelativeFundamentalWeightStatement` (V.3.12, simple coroots and fundamental
  weights and coweights);
- `StandardLeviRealDecompositionStatement` (V.3.13, corrected);
- `RelativeRealCorootLinearAlgebraStatement`, the conjunction of the four.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The passages
were read in the original PDF:

- V.3.3 and V.3.4, printed p.110 / PDF p.116: `𝔞 = X_*(A) ⊗ ℝ`,
  `𝔞^* = X^*(A) ⊗ ℝ`, the roots `Σ'(A)` and the reduced roots
  `Σ(A) = {α ∈ Σ'(A) | α/n ∉ Σ'(A) for n ≥ 2}`;
- V.3.6 and V.3.7, printed p.111 / PDF p.117: `𝔞_M = 𝔞_G ⊕ 𝔞^G_M`, the
  `W`-invariant scalar products, the coroot `α̌` defined by
  `⟨α̌, λ⟩ = 2 (α, λ) / (α, α)`, the root systems `Σ(A_M)` and `Σ^∨(A_M)` for a
  minimal parabolic, and the sentence "Les racines (resp. les coracines)
  engendrent le sous-espace `(𝔞^G_M)^*` (resp. `𝔞^G_M`)";
- V.3.12, printed p.112 / PDF p.118: `Δ_∅` is a basis of `(𝔞^G_∅)^*`, `Δ^∨_∅`
  is a basis of `𝔞^G_∅`, the fundamental weights `ϖ_α` (the basis of
  `(𝔞^G_∅)^*` dual to `Δ^∨_∅`) and the fundamental coweights `ϖ^∨_α` (the basis of
  `𝔞^G_∅` dual to `Δ_∅`);
- V.3.13, printed pp.112–113 / PDF pp.118–119: `𝔞_M` is the orthogonal of the
  roots in `Δ^M_∅`, `𝔞^*_M` the orthogonal of the coroots, the decompositions
  `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅`, `𝔞^*_∅ = 𝔞^*_G ⊕ (𝔞^G_∅)^*`,
  `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*` and their duals, which "sont orthogonales pour le
  produit scalaire fixé".

## Setting and spaces

All four statements quantify over a field `k : Type u`, a connected reductive
group scheme `G` over `Spec k`, and a maximal split torus `i : T.toGrp ⟶ G`
(`IsMaximalSplitTorus i`). This `T` is the book's `A_∅`, the split component of
the minimal Levi subgroup `M_∅ = Z_G(A_∅)`. The real spaces are the published
ones of `Langlands.GroupScheme.RealTorusSpace`:

- `𝔞_∅ = V T = ℝ ⊗[ℤ] cocharacterLattice T`;
- `𝔞^*_∅ = Vstar T = ℝ ⊗[ℤ] characterLattice T`;
- `pair T : Vstar T →ₗ V T →ₗ ℝ`, the real extension of the lattice pairing,
  and `eval T α`, the evaluation of a character `α` on `V T`.

The roots `Σ'(A_∅)` are the published `relativeRoots i`, possibly
nonreduced. The reduced roots `Σ(A_∅)` of V.3.4 are the published
`RelativeRoot.indivisibleRoots i`: the roots `a` such that `m • b ≠ a` for every
root `b` and every natural number `m > 1`. Because the character lattice is free,
this is the book's condition `α/n ∉ Σ'(A_∅)`.

The minimal parabolic `P_∅` is fixed, as in the Library, by a generic cocharacter
`ν` (`IsGenericCocharacter i ν`: no root vanishes on `ν`). Its simple roots `Δ_∅`
are the published `simpleRelativeRoots i ν`, the positive roots that are not sums
of two positive roots. In a nonreduced system the divisible roots `2α` are sums
`α + α`, so these are the simple roots of the reduced system `Σ_∅`, as in the
book. A standard Levi subgroup `M` is recorded by its simple-root set
`J = Δ^M_∅ ⊆ Δ_∅`, and `M ⊆ L` by `J ⊆ K ⊆ Δ_∅`.

The relative Weyl group `W(A_∅)` is the published `relativeWeylGroup i`. It acts
on `𝔞^*_∅` by `relativeWeylFullRealAction i` and on `𝔞_∅` by
`relativeWeylRealAction i`.

### Coroots come from reflection data

The coroots are taken from published integral reflection data
`D : RelativeRootReflectionData i`. For each root `α` it gives an integral
cocharacter `D.coroot α` with `⟨α, D.coroot α⟩ = 2` and a normalizing rational
point `D.representative α` acting on characters by
`χ ↦ χ - ⟨χ, D.coroot α⟩ α`. This is input data, not an existence assertion.
The existence of such data is the published
`RelativeRootReflectionExistenceStatement`. Each statement that uses coroots
quantifies over every `D`. `RelativeRealCorootStatement` asserts that the
coroots do not depend on `D`, and that they satisfy the book's defining formula
for every invariant scalar product. So the book's coroot, defined by that
formula, is `D.realCoroot α` for every choice of `D`.

## Definitions

In the variable context `i : T.toGrp ⟶ G` with `[IsAffineHom G.X.hom]`, and
`[Mono i.hom.hom.left]` where stated.

- `simpleToRelativeRoot i ν : simpleRelativeRoots i ν → relativeRoots i` is the
  inclusion of the simple roots among the roots. `simpleRelativeRoots_subset_relativeRoots`
  is its supporting inclusion.
- `IsRealFundamentalCoweight i ν α v` (V.3.12, `ϖ^∨_α`): `v` lies in
  `𝔞^G_∅ = cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))`,
  `eval T α v = 1`, and `eval T β v = 0` for every other simple root `β`. Here
  `𝔞^G_∅` is the book's V.3.6 space for `M = M_∅`: the cocharacters annihilated
  by the restrictions to `A_∅` of the real rational characters of `G`.
- `IsWeylInvariantCocharacterInnerProduct i C` (V.3.7, the scalar product on
  `𝔞_∅`): `C` is symmetric, positive definite and invariant under
  `relativeWeylRealAction i`. It is the cocharacter-side companion of the published
  `IsWeylInvariantInnerProduct i B` on `𝔞^*_∅`.
- `D.realCoroot α : V T` (V.3.7, `α̌`) is `1 ⊗ D.coroot α`.
  `pair_tmul_realCoroot` computes its pairing with a pure tensor, and
  `pair_root_realCoroot` gives `⟨α, α̌⟩ = 2`.
- `D.realCorootSpan` is the real span of all the coroots, the book's span of
  `Σ^∨(A_∅)`.
- `D.realCorootsOf J` is the set of the coroots of the roots in `J`.
- `D.IsRealFundamentalWeight ν α x` (V.3.12, `ϖ_α`): `x` lies in
  `(𝔞^G_∅)^* = relativeRootSpanReal i`, `⟨x, α̌⟩ = 1`, and `⟨x, β̌⟩ = 0` for every
  other simple root `β`.
- `D.leviRootSpace J K` (V.3.13 corrected, `(𝔞^L_M)^*`) is
  `corootAnnihilator i D J ⊓ span_ℝ K`. The published `corootAnnihilator i D J`
  is the book's `𝔞^*_M`: the characters annihilating the coroots of `J`.
- `D.projectedRoots J S` is the set of projections to `𝔞^*_M` of the roots in
  `S`, along the real span of `J`. It is the set of `y ∈ 𝔞^*_M` such that
  `α - y ∈ span_ℝ J` for some `α ∈ S`.
- `D.leviCorootSpace J K` (V.3.13, `𝔞^L_M`) is
  `rootAnnihilator T J ⊓ span_ℝ (D.realCorootsOf K)`. The published
  `rootAnnihilator T J` is the book's `𝔞_M`: the cocharacters on which the roots
  of `J` vanish.
- `D.projectedCoroots J S` is the dual of `projectedRoots`: the projections to
  `𝔞_M` of the coroots of `S`, along the real span of the coroots of `J`.

The book does not name the projection maps `p^L_M` separately. They are the
projections of the direct sums asserted below, for example
`Submodule.linearProjOfIsCompl`, so they need no further definition here.

## Statements

### `RelativeRealSimpleRootBasisStatement` (V.3.12, roots)

For every generic `ν` there is a basis `b` of `relativeRootSpanReal i`, indexed by
`simpleRelativeRoots i ν`, with `b α = 1 ⊗ α`. This says that `Δ_∅` is a basis of
`(𝔞^G_∅)^*`. The published `RelativeSimpleRootBasisStatement` gives the rational
version, a basis of `relativeRootSpan i` over `ℚ`. The real version is its scalar
extension, but it is not in the Library.

### `RelativeRealCorootStatement` (V.3.7 for the minimal parabolic)

For every reflection data `D`:

1. a `W`-invariant scalar product exists on `𝔞^*_∅`
   (`IsWeylInvariantInnerProduct i B`) and one exists on `𝔞_∅`
   (`IsWeylInvariantCocharacterInnerProduct i C`). The book assumes both spaces
   carry such products ("On supposera … toujours munis de produits scalaires");
2. every reflection data `D'` has `D'.coroot = D.coroot`;
3. for every invariant `B`, every root `α` and every `v : V T`, the formula
   `⟨λ, v⟩ (α, α) = 2 (α, λ)` holds for all `λ ∈ 𝔞^*_∅` exactly when
   `v = D.realCoroot α`. This is the book's definition of `α̌`, written without
   dividing by `(α, α)`. The "if" direction is the published theorem
   `RelativeRootReflectionData.coroot_mul_form`; the content added here is
   uniqueness, which uses the perfect pairing of `𝔞^*_∅` with `𝔞_∅`;
4. the coroots span `𝔞^G_∅`, the cocharacter annihilator of the restricted real
   rational characters of `G` (V.3.7, last sentence, for `M = M_∅`);
5. `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅`, as `IsCompl`, with `𝔞_G` the published common root
   annihilator `relativeCentralDirections i` (V.3.6 and V.3.13 for `M = M_∅`);
6. the set of roots is finite;
7. there is a Mathlib `RootPairing` indexed by all roots, on `relativeRootSpanReal i`
   and `D.realCorootSpan`. It is a crystallographic root system, its roots are the
   `1 ⊗ α` and its coroots the `α̌`, and its pairing is `pair T`. Its reflections and
   coreflections are the actions of the representatives `D.representative α` on
   `𝔞^*_∅` and `𝔞_∅`. This is the book's "`Σ(A_M)` est un système de racines" and
   "`Σ^∨(A_M)` est un système de racines dans `𝔞_M`", for the possibly nonreduced
   `Σ'`. The coroot system is the coroot side of the same root pairing;
8. there is also a reduced crystallographic root system indexed by the indivisible
   roots `Σ(A_∅)`, with the same roots, coroots and pairing. This is V.3.7
   exactly as printed, with the reduced roots of V.3.4.

Neither space need be spanned: the root system lives on the root span and the
coroot span, as in the book's V.3.7. Item 7 covers nonreduced relative root
systems. Its reflection clause identifies the reflection of each root with an
element of `W(A_∅)`. The converse identification, that `W(A_∅)` is generated by
these reflections ("on peut par ce biais identifier `W(A_M)` au groupe de Weyl"),
is not restated. It is covered by the published `HasRelativeRootSystem` (rational
form) and `RelativeWeylCoxeterStatement`.

### `RelativeFundamentalWeightStatement` (V.3.12, coroots and weights)

For every generic `ν` and every `D`:

1. the simple coroots form a basis of `𝔞^G_∅`;
2. there is a basis of `(𝔞^G_∅)^* = relativeRootSpanReal i`, indexed by the simple
   roots, whose `α`-th vector satisfies `IsRealFundamentalWeight` for `α`. This is
   the book's basis dual to `Δ^∨_∅`;
3. there is a basis of `𝔞^G_∅`, indexed by the simple roots, whose `α`-th vector
   satisfies `IsRealFundamentalCoweight` for `α`. This is the book's basis dual
   to `Δ_∅`;
4. each simple root has at most one fundamental weight and at most one
   fundamental coweight.

With (2) and (3) this makes `ϖ_α` and `ϖ^∨_α` well-defined vectors, as in the
book.

### `StandardLeviRealDecompositionStatement` (V.3.13, corrected)

For every generic `ν` and every `D`, with `Δ = simpleRelativeRoots i ν`:

1. `𝔞^*_G`, the coroot annihilator `corootAnnihilator i D Δ` of all simple roots,
   equals the range of the real restriction of rational characters of `G`;
2. `𝔞_G`, the annihilator `rootAnnihilator T Δ` of the simple roots, equals the
   common root annihilator `relativeCentralDirections i`;
3. the simple coroots span `𝔞^G_∅`.

For all `J ⊆ K ⊆ Δ` (standard Levi subgroups `M ⊆ L`):

4. `𝔞^*_∅ = 𝔞^*_M ⊕ span_ℝ J` and `𝔞_∅ = 𝔞_M ⊕ span_ℝ J^∨`;
5. the pairing restricts to a perfect pairing of `𝔞^*_M` with `𝔞_M`, as
   `LinearMap.IsPerfPair` of `(pair T).domRestrict₁₂`. So the book's two
   descriptions of `𝔞_M` and `𝔞^*_M` in V.3.13 are dual spaces, as their notation
   says;
6. `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*`, stated as `Disjoint` together with a supremum
   equation inside `𝔞^*_M`. Moreover `(𝔞^L_M)^*` is spanned by the projections
   to `𝔞^*_M` of the roots in `K ∖ J`;
7. dually, `𝔞_M = 𝔞_L ⊕ 𝔞^L_M`, with `𝔞^L_M` spanned by the projections to `𝔞_M`
   of the coroots of `K ∖ J`;
8. both decompositions are orthogonal for every invariant scalar product `B` on
   `𝔞^*_∅`, resp. `C` on `𝔞_∅`.

The case `J = ∅` gives `corootAnnihilator i D ∅ = ⊤` and `rootAnnihilator T ∅ = ⊤`,
so with `K = Δ` items 6–8 contain the book's
`𝔞^*_∅ = 𝔞^*_G ⊕ (𝔞^G_∅)^*` and `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅`, and their orthogonality.
Here `(𝔞^G_∅)^* = span_ℝ Δ` and `𝔞^G_∅ = span_ℝ Δ^∨`, as in the book. With
`K = Δ` and arbitrary `J`, item 6 is the book's `𝔞^*_M = 𝔞^*_G ⊕ (𝔞^G_M)^*`,
with `(𝔞^G_M)^*` spanned by the projected roots. This is also the book's V.3.14
remark that `(𝔞^G_M)^*` is spanned by `Δ(P)`, the restrictions of the roots of
`Δ_∅ ∖ Δ^M_∅` to `𝔞_M`. The span of `J` vanishes on `𝔞_M`, so a root and its
projection to `𝔞^*_M` have the same restriction to `𝔞_M`. By item 5 the projection
is determined by that restriction.

## Source issue I4 and its correction

As printed, V.3.13 defines `(𝔞^L_M)^*` as the subspace of `𝔞^*_∅` spanned by the
`α ∈ Δ^L_∅ ∖ Δ^M_∅`, and states `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*`. With
`𝔞^*_M ⊂ 𝔞^*_∅` the annihilator of the coroots of `M`, as V.3.13 itself says,
this is false. Take `G = L = GL_3` and `M = GL_2 × GL_1` standard, with
`Δ_∅ = {α_1, α_2}` and `Δ^M_∅ = {α_1}`. Then `𝔞^*_M = {(x, x, y)}`, but
`α_2 = (0, 1, -1)` pairs with `α̌_1 = (1, -1, 0)` to `-1`, so `α_2 ∉ 𝔞^*_M`. The
same failure occurs for the dual decomposition of `𝔞_M`. This is issue I4 of the
public Chapter V ledger `notes/renard/item-ledger-v.md`.

The statement here uses the corrected subspace. `(𝔞^L_M)^*` is the part of
`𝔞^*_M` in the span of `K`, and it is proved, not assumed, to be spanned by the
projections of the roots of `K ∖ J`. This matches the definition of `Δ(P)` by
restriction to `𝔞_M` in V.3.14. When `J = ∅` the printed and corrected subspaces
coincide (both are `span_ℝ K`). The orthogonality clauses are stated for the
corrected spaces.

## Choices and qualifications

- **Arbitrary fields.** The book works over a nonarchimedean local field. These
  statements are linear algebra on the actual real character and cocharacter
  spaces, so they are stated over every field with no topology. This is a
  generalization, not a weakening.
- **Spaces of standard Levi subgroups.** As in V.3.13, `𝔞_M` and `𝔞^*_M` are the
  root and coroot annihilators of `J` inside `𝔞_∅` and `𝔞^*_∅`. Their
  identification with `X_*(A_M) ⊗ ℝ` and `X^*(A_M) ⊗ ℝ` for the actual split
  component `A_M` is not restated here. For that, see the published
  `RenardLeviCentralDecompositionStatement` (V.3.6 for arbitrary compatible split
  components) and the published standard-Levi split-component and annihilator
  files.
- **Every scalar product.** The book fixes one invariant scalar product. Here
  existence is asserted, and the coroot formula and orthogonality are asserted
  for every invariant scalar product. This is stronger than the book's claim for
  the fixed product, so the book's version follows. The two products on `𝔞_∅` and
  `𝔞^*_∅` are not required to be dual to each other. Orthogonality holds for each
  separately.
- **Minimal parabolic only, in V.3.7.** The book asserts the root-system
  statements of V.3.7 only for minimal `P`. For a standard `M`, the spanning
  sentence of V.3.7 is covered by items 6 and 7 of the Levi statement with
  `K = Δ`.
- **Relation to published work.** `HasRelativeRootSystem` (Library
  `Langlands.GroupScheme.Rational.Statement`) is a rational root system on
  `relativeRootSpan i` with the dual space as coroot space. It records neither the
  real coroots in `𝔞_∅` nor their span. The published `LanglandsInvariantForm`
  proves the coroot formula for a given invariant `B` (`coroot_mul_form`,
  `coroot_formula`) and is reused, not duplicated. `corootAnnihilator` and
  `IsWeylInvariantInnerProduct` come from `LanglandsDecompositionCones`. A
  candidate invariant form on `𝔞^*_∅` is the published
  `RealTorusSpace.relativeWeylInvariantForm`. The published fundamental weights
  in `GroupScheme/Torus/FundamentalWeightPermutation` and
  `GroupScheme/Rational/FundamentalRepresentations` are integral weights of an
  absolute root datum, not the real relative weights of V.3.12. The published
  `RelativeCharacterRootComplementStatement` gives the character-side complement
  `𝔞^*_∅ = (𝔞^G_∅)^* ⊕ 𝔞^*_G` with `𝔞^*_G` the restricted-character range.
- **Provenance.** Items stated by the book are source content. The following are
  derived and are stated because the book's sentences need them to make sense:
  the `D`-independence of the coroots, the existence of the scalar products, the
  finiteness of the roots, the perfect pairing of item 5, and the
  nonreduced-system root pairing of item 7. Their proofs are standard: Bourbaki's
  uniqueness of a reflection preserving a finite spanning set, Weyl averaging,
  and finite-dimensional duality.

## Proof obligations

No proof is included. After publication, proof tasks for the four component
statements (or for `RelativeRealCorootLinearAlgebraStatement`) will be published
separately.
