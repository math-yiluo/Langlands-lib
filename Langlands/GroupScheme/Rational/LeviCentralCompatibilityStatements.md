# Split components of nested Levis and characters of standard Levis

Worker 4, for Task 1222. Module
`Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements`, namespace
`Langlands.GroupScheme`, universe parameter `u` (the base field).

This file states two geometric facts that Renard V.3.6 and V.3.13 use. The
published linear algebra for those sections takes them as inputs. The file
contains three `Prop`-valued statement definitions and proves none of them:

- `LeviSplitComponentInclusionStatement`: for rational Levi subgroups
  `M ⊆ L`, the split component `A_L` lies in `A_M` (V.3.6 `A_G ⊂ A_M`, V.3.13
  `A_G ⊂ A_L ⊂ A_M ⊂ A_∅`);
- `StandardLeviCharacterAnnihilatorStatement`: for a standard Levi `M`, the
  real characters of `M`, restricted to the maximal split torus, are exactly
  the real characters of the torus that vanish on the coroots of `M`
  (V.3.13, `𝔞*_M ⊂ 𝔞*_∅` described by coroots);
- `LeviCentralCompatibilityStatements`, the conjunction of the two.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

V.3.6, printed p. 111 / PDF p. 117:

> Soit `P = MN` un sous-groupe parabolique de `G`, de composante déployée
> `A_M`. Soit `A_G` la composante déployée de `G`. On a
> `A_G ⊂ A_M ⊂ M ⊂ G`, ce qui induit des morphismes donnés par la
> restriction des caractères […]

V.3.13, printed p. 112 / PDF p. 118:

> Soient `P = MN ⊂ Q = LU` deux sous-groupes paraboliques standards de `G`.
> On a alors `A_G ⊂ A_L ⊂ A_M ⊂ A_∅` et `𝔞_G ⊂ 𝔞_L ⊂ 𝔞_M ⊂ 𝔞_∅` où `𝔞_G`
> (resp. `𝔞_M`, resp. `𝔞_L`) est l'orthogonal des racines `α ∈ Δ_∅`
> (resp. `Δ^M_∅`, resp. `Δ^L_∅`). De même `𝔞*_G ⊂ 𝔞*_L ⊂ 𝔞*_M ⊂ 𝔞*_∅`
> sont décrits de la même manière en remplaçant les racines par les
> coracines.

Renard gives no proof of these inclusions. The sections recall Borel–Tits
and Springer (V.3, printed p. 109 / PDF p. 115).

## Published objects used

- `IsConnectedReductive`, `IsParabolicSubgroup p` for `p : P ⟶ G`, and
  `IsRationalLeviSubgroup l` for `l : M ⟶ P`: a connected reductive group
  over the field `k`, a parabolic subgroup defined over `k`, and a Levi
  factor of it defined over `k` (a closed connected reductive subgroup `M`
  with `M ⋉ U ≅ P` for the unipotent radical `U`).
- `IsSplitComponent a` for `a : A ⟶ M`: Renard's *composante déployée*
  `A_M`, a central split torus of `M` that admits no proper enlargement to a
  central split torus.
- `CommGroupScheme.groupHom f`: the group-scheme morphism underlying a
  morphism `f : A ⟶ A'` of commutative group schemes.
- `IsMaximalSplitTorus i`, `IsGenericCocharacter i ν`,
  `simpleRelativeRoots i ν` and `standardLevi i ν J`: a maximal split torus
  `i : T ⟶ G` (Renard's `A_∅`), a generic cocharacter selecting the positive
  relative roots, its simple roots `Δ_∅`, and the standard Levi subgroup
  functor of a set `J ⊆ Δ_∅` (Renard's `M`, with `Δ^M_∅ = J`).
- `RelativeRootReflectionData i`: integral reflection data for the relative
  roots, which supply the coroots `D.coroot α`. The published
  `RelativeRealCorootStatement` (proved) shows that their real images do not
  depend on `D`.
- `rationalCharacterRestrictReal t`: for `t : T ⟶ L`, restriction of
  rational characters along `t`, tensored with `ℝ`:
  `ℝ ⊗ X*(L) → ℝ ⊗ X*(T)`.
- `corootAnnihilator i D J`: the real characters `y` of `T` with
  `⟨y, α̌⟩ = 0` for every relative root `α ∈ J`. This is the published
  ambient model of `𝔞*_M ⊂ 𝔞*_∅` (module `LanglandsDecompositionCones`).

## The statements

### `LeviSplitComponentInclusionStatement`

Let `G` be connected reductive over a field `k`. Let `p : P ⟶ G` and
`q : Q ⟶ G` be parabolic subgroups, `lM : M ⟶ P` and `lL : L ⟶ Q` rational
Levi factors, and `m : M ⟶ L` with `m ≫ lL ≫ q = lM ≫ p`, so that `M ⊆ L`
inside `G`. For any split components `aL : A_L ⟶ L` and `aM : A_M ⟶ M` there
is a homomorphism `f : A_L ⟶ A_M` with `f ≫ aM ≫ m = aL`.

The parabolic subgroups `P` and `Q` are not required to be nested; only
`M ⊆ L` is assumed.

Special cases:

- **V.3.6.** Take `Q = L = G` and `q = lL = 𝟙 G`. These are a parabolic
  subgroup and a rational Levi factor by the published
  `IsConnectedReductive.isParabolicSubgroup_id` and
  `IsConnectedReductive.isRationalLeviSubgroup_id`. With `m = lM ≫ p`, the
  conclusion is `f ≫ aM ≫ lM ≫ p = aG`. This is the compatible diagram that
  the published `RenardLeviCentralDecompositionStatement` (proved by
  `renardLeviCentralDecomposition`) assumes, for `j = lM ≫ p`. `M` is
  connected reductive by `IsRationalLeviSubgroup.isConnectedReductive`. So
  the two statements together give V.3.6 for every rational Levi factor and
  every choice of split components.
- **V.3.13.** For standard parabolic subgroups `P ⊆ Q` with Levi factors
  `M ⊆ L`, the statement gives `A_L ⊂ A_M`. With `L = G` it gives
  `A_G ⊂ A_L`. The inclusion `A_M ⊂ A_∅` into the maximal split torus is the
  published `StandardLeviSplitCentralDirectionsStatement`.

### `StandardLeviCharacterAnnihilatorStatement`

Let `G` be connected reductive over `k`, `i : T ⟶ G` a maximal split torus,
`ν` a generic cocharacter of `T`, and `J` a set of simple relative roots for
`ν`. Let `j : L ⟶ G` be a closed subgroup representing the standard Levi
subgroup of `J`, and `t : T ⟶ L` with `t ≫ j = i`. For all integral
reflection data `D`,

`(rationalCharacterRestrictReal t).range = corootAnnihilator i D J`.

That is, the image of `𝔞*_L = ℝ ⊗ X*(L)` in `𝔞*_∅ = ℝ ⊗ X*(T)` under
restriction is the annihilator of the coroots `α̌`, `α ∈ J = Δ^L_∅`. With
`J = Δ_∅` this is the description of `𝔞*_G` (here `L = G`).

### `LeviCentralCompatibilityStatements`

The conjunction of the two statements above, at the same universe `u`.

## Formal choices

- **Arbitrary field.** Both statements are over an arbitrary field `k` of
  universe `u`, as are the published V.3.6 and V.3.13 statements they
  complete. Renard's field is nonarchimedean local. The inclusions hold
  over every field (see below).
- **Inclusions as factorizations.** "`A_L ⊂ A_M`" is stated as the
  existence of a homomorphism `f` through which `aL` factors. Since
  `aM ≫ m` is a monomorphism, such an `f` is unique and is a closed
  subgroup; neither fact is asserted.
- **Every choice of split components.** Both `A_L` and `A_M` are arbitrary
  split components, so the statement does not depend on choosing them.
- **Identification of `𝔞*_M` with a subspace of `𝔞*_∅`.** Renard identifies
  `𝔞*_M` with a subspace of `𝔞*_∅` through restriction of characters from
  `M` to its subgroups. The statement uses restriction from `L` to the
  maximal split torus `T`. Restriction from `L` to `A_L` is bijective after
  tensoring with `ℝ` (V.3.6, published), and `A_L ⊆ T`, so this is the same
  identification.
- **Coroots from reflection data.** The coroots are those of the supplied
  `D`, as in the published standard-Levi statements. Their real images do
  not depend on `D`.

## Why the statements are true

**Inclusion.** Identify `M` with its image in `L` under `m`. By the
published `LeviCentralizerCharacterizationStatement` (proved by
`leviCentralizerCharacterization`), the rational Levi factor `lM ≫ p` is the
whole centralizer of a split subtorus `A ⊆ M` of `G`. `A_L` is central in
`L`, and `A ⊆ M ⊆ L`, so `A_L` centralizes `A`. Hence `aL ≫ lL ≫ q`
factors through the centralizer, that is, through `lM ≫ p`. Since
`m ≫ lL ≫ q = lM ≫ p` and `lL ≫ q` is a monomorphism, this gives
`g : A_L ⟶ M` with `g ≫ m = aL`. (Alternatively, the proved
`LeviSplitComponentCentralizerStatement`, `Z_G(A_M) = M`, gives the same
factorization with `A = A_M`.) Then `g` is central in `M`, because `aL` is
central in `L` and `m` is a monomorphism. A central split torus of `M`
factors through every split component of `M` (published
`IsSplitComponent.exists_factor`), which gives `f` with `f ≫ aM = g`.

**Characters.**

1. *Image in the annihilator.* Let `χ` be a rational character of `L` and
   `α ∈ J`. The reflection `s_α` lies in the relative Weyl group of `L`, so
   it is realized by an element `n ∈ N_L(T)(k)`. The restriction `χ|_T` is
   invariant under conjugation by `n`, so `s_α(χ|_T) = χ|_T`. Since
   `s_α(y) = y − ⟨y, α̌⟩ α` and `α ≠ 0`, this gives `⟨χ|_T, α̌⟩ = 0`.
2. *Equality.* Let `a : A_L ⟶ L` be a split component. The published
   `StandardLeviSplitCentralDirectionsStatement` gives `f : A_L ⟶ T` with
   `f ≫ i = a ≫ j`, hence `f ≫ t = a`. It also gives
   `rank X*(L) = rank A_L` and `rank T = |J| + rank A_L`. Restriction from
   `L` to `A_L` is bijective after tensoring with `ℝ` (Renard's Lemma V.2.6;
   for instance the second conjunct of the proved
   `RenardLeviCentralDecompositionStatement`, applied to `𝟙 L`). It
   factors through restriction along `t`, so restriction along `t` is
   injective and its range has dimension `rank T − |J|`. The simple coroots
   are linearly independent, so `corootAnnihilator i D J` also has
   dimension `rank T − |J|`. With step 1 the two spaces are equal.
   Alternatively, the published `langlandsCharacterRestriction` shows that
   restriction along `f` maps the annihilator bijectively onto `ℝ ⊗ X*(A_L)`
   when a compatible parabolic presentation is given. This gives the same
   equality.

## Relation to the Library

- `RenardLeviCentralDecompositionStatement` (proved) proves the V.3.6
  decompositions for any morphism `j : M ⟶ G` whose split components fit
  into a compatible diagram. It assumes the diagram;
  `LeviSplitComponentInclusionStatement` supplies it for every rational
  Levi factor.
- `leviSplitComponent_factorization` (module `LeviSplitComponentFactorization`)
  constructs *some* split component of a dynamic Levi subgroup through which
  `A_G` factors. The present statement concerns arbitrary rational Levi
  factors, nested pairs `M ⊆ L`, and every split component.
- `StandardLeviSplitCentralDirectionsStatement` (proved) gives
  `A_M ⊂ A_∅` and the cocharacter side `𝔞_M ⊂ 𝔞_∅` of V.3.13.
  `StandardLeviCharacterAnnihilatorStatement` is the character side.
- `langlandsCharacterRestriction` compares `ℝ ⊗ X*(A_M)` with the annihilator
  through the split component. The present statement compares the
  characters of `M` themselves.
- Worker 1222's `LeviSplitComponentCentralizerStatement` (`Z_G(A_M) = M`)
  is proved by `leviSplitComponentCentralizer` (module
  `LeviSplitComponentCentralizerProof`, Task 6918). Neither statement of
  this file restates it. The proof sketch above uses the proved
  `LeviCentralizerCharacterizationStatement`; `leviSplitComponentCentralizer`
  gives an alternative first step.

## Proof obligations

The proofs of `LeviSplitComponentInclusionStatement`,
`StandardLeviCharacterAnnihilatorStatement` and their conjunction are
separate proof obligations of the whole-book task.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements` | `IsParabolicSubgroup`, `IsRationalLeviSubgroup`, `IsSplitComponent` (through its imports) |
| `Langlands.GroupScheme.Rational.LanglandsDecompositionCones` | `corootAnnihilator`; through its imports `RelativeRootReflectionData`, `rationalCharacterRestrictReal`, `standardLevi`, `simpleRelativeRoots`, `IsGenericCocharacter` |
