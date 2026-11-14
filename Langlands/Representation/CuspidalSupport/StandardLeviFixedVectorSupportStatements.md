# Compact open subgroups and standard Levi subgroups in the Bernstein decomposition (Renard VI.10.6, Corollary; statements)

Module `Langlands.Representation.CuspidalSupport.StandardLeviFixedVectorSupportStatements`.
Namespace `Langlands.CuspidalSupport`. Universe parameters: `uF` (the field and the group
schemes) and `uV` (representation carriers, always used at the saturated universe
`max uF uV` of the published Bernstein framework).

The module contains three `Prop`-valued definitions. None of them is proved here.

- `StandardLeviCompactInheritanceStatement`: the sentence before the Corollary,
  "`K_M = K ∩ M` possède les mêmes propriétés que `K` relativement au groupe `M`".
- `StandardRepresentativeFixedVectorCriterionStatement`: the first claim of the proof of the
  Corollary, for a standard cuspidal datum `a = (M_I, σ)`: `[a]_G ∈ B(G)_K` iff `σ` has a
  nonzero `K ∩ M_I`-fixed vector.
- `StandardLeviFixedVectorSupportStatement`: the Corollary,
  `B(M)_{K_M} = i_{MG}^{-1}(B(G)_K)`, for every standard Levi `M = M_J`.

The module also has three `local instance`s (closed immersion, affineness and local finite
type of the standard Levi schemes `bernsteinLeviScheme i ν I`). They are verbatim copies of the
local instances of the published module `BernsteinData` (`bernsteinLeviClosedImmersion`,
`bernsteinLeviAffine`, `bernsteinLeviFiniteType`). They are needed only so that the published
`IsRationalInertiaRelated` (unramified characters of the Levi scheme) elaborates in the last
statement, exactly as it does in the published `IsBernsteinInertiaRelated`. No new object is
defined.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
It covers gap 4 of the Chapter VI item ledger (`notes/renard/item-ledger-vi.md`, row
"VI.10.6 Corollary"). The ledger records that gap as blocked because it seemed to need
Bernstein data for a Levi subgroup `M`. This unit does not need them: it uses the convention of
the published `BernsteinInductionRestrictionStatement` (Renard VI.7.3, the source of the map
`i_{MG}`), as explained in "Cuspidal data and inertial classes of `M`" below.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF page numbers are
one-based and equal printed page numbers plus six. The author read VI.10.5–VI.10.7,
printed pp.213–215 / PDF pp.219–221, and VI.7.3, printed p.185 / PDF p.191.

**`B(G)_K` (VI.10.6, Theorem, printed p.213 / PDF p.219).**

> Plus précisément, pour un tel `K`, notons `Irr(G)_K` l'ensemble des classes d'équivalence de
> représentations lisses irréductibles de `G` admettant des vecteurs fixés par `K` non nuls, et
> `Ω(G)_K` l'ensemble de leurs supports cuspidaux. Alors `Ω(G)_K` est un ensemble fini de
> composantes connexes de `Ω(G)` (et l'on note `B(G)_K` leurs support d'inertie).

The proof of this Theorem (printed pp.213–214 / PDF pp.219–220) contains the computation that
the Corollary's proof refers to as "la démonstration du théorème":

> Soit maintenant `𝔰 = [M, (ρ, W)]_G ∈ B(G)` et soit `D` la classe d'inertie de `(ρ, W)` dans
> `M`. Pour tout `ψ ∈ X(M)`, on peut identifier `i_P^G(ρψ, W)^K` a un espace ne dépendant pas de
> `ψ`. En effet, d'après le lemme III.2.2,
> `i_P^G(ρψ, W)^K ≃ ⊕_{ḡ ∈ P\G/K} W^{p(K_g)}`,
> où `K_g = P ∩ gKg^{-1}` et `p` désigne la projection de `P` sur `P/N ≃ M`. [...] De plus
> `𝔰 ∈ B(G)_K` si et seulement si `D ∈ B(M)_{p(K_g)}` pour un certain `ḡ ∈ P\G/K`.

**The class of `K` (VI.10.6, Proposition, printed p.214 / PDF p.220).**

> Soit `K` est un sous-groupe ouvert compact de `G`, inclus et distingué dans `K₀` et admettant
> une décomposition d'Iwahori selon les sous-groupes paraboliques standards.

**The inheritance sentence and the Corollary (printed pp.214–215 / PDF pp.220–221).**

> Soit `K` un sous-groupe ouvert compact de `G`, inclus et distingué dans `K₀` et admettant une
> décomposition d'Iwahori selon les sous-groupes paraboliques standards et soit `P = MN` un
> sous-groupe parabolique standard. Alors `K_M = K ∩ M` possède les mêmes propriétés que `K`
> relativement au groupe `M`. Reprenons les notations de la section VI.7.3.
>
> **Corollaire.** La partie `B(M)_{K_M}` de `B(M)` est l'image inverse par `i_{MG}` de la partie
> `B(G)_K`.
>
> *Démonstration.* Soit `𝔰 = [M, (σ, E)]_G ∈ B(G)`. Montrons que `𝔰 ∈ B(G)_K` si et seulement
> si `𝔱 = [M, σ]_M ∈ B(M)_{K_M}`. Supposons `𝔱 = [M, σ]_M ∈ B(M)_{K_M}`, c'est-à-dire que `E`
> admet des vecteurs fixes par `K_M` non nul. Considérons la représentation `π = i_P^G(σ)`,
> d'espace `V`. Comme d'après le lemme de Jacquet, `V^K` se surjecte sur `V_N^{K_M}` qui
> contient un sous-quotient isomorphe à `E^{K_M}` d'après le lemme géométrique, on a
> `V^K ≠ 0`. Donc il existe une représentation irréductible dans `M(G)_𝔰` dans `M(G)_K`, ce qui
> montre d'après ce qui précède que `M(G)_𝔰 ⊂ M(G)_K`, et donc `𝔰 ∈ B(G)_K`. Réciproquement, si
> `𝔰 ∈ B(G)_K`, d'après la démonstration du théorème, `E^{p(K_g)} ≠ 0` pour un certain
> `g ∈ G`. Ecrivons `g = pk`, avec `k ∈ K₀` et `p ∈ P`. Alors, comme `K` est supposé distingué
> dans `K₀`, `K_g = gKg^{-1} ∩ P = pkKk^{-1}p^{-1} ∩ P = p(K ∩ P)p^{-1}` et tous les `p(K_g)`
> sont conjugués (à `K_M`) dans `M`. Donc `E^{K_M} ≠ 0`. Démontrons maintenant le corollaire.
> Soit `𝔱 ∈ B(M)` et montrons que `𝔱 ∈ B(M)_{K_M}` si et seulement si `i_{MG}(𝔱) ∈ B(G)_K`. On
> a `𝔱 = [L, σ]_M` pour un certain sous-groupe de Levi standard `L` inclus dans `M`. Si
> `𝔱 ∈ B(M)_{K_M}`, alors `σ` admet un vecteur non nul fixé par `K_L = K ∩ L`, et
> `i_{MG}(𝔱) = [L, σ]_G` admet un vecteur non nul fixé par `K`, donc `i_{MG}(𝔱) ∈ B(G)_K`.
> Réciproquement, si `i_{MG}(𝔱) ∈ B(G)_K`, alors `σ` admet un vecteur non nul fixé par
> `K_L = K ∩ L` et donc `𝔱 ∈ B(M)_{K_M}`.

**`i_{MG}` (VI.7.3, printed p.185 / PDF p.191)**, quoted in full in the Markdown of the
published `BernsteinInductionRestrictionStatement`: a cuspidal datum `(L, (σ, E))` of `M` is a
cuspidal datum of `G`, and `i_{MG} : B(M) → B(G)`, `[L, (σ, E)]_M ↦ [L, (σ, E)]_G`.

In the first claim of the proof, `σ` is supercuspidal on `M`, so the irreducible
representations of `M` with inertial support `[M, σ]_M` are the unramified twists `σψ`, and
`(σψ)^{K_M} = σ^{K_M}` because the unramified character `ψ` is trivial on the compact group
`K_M`. That is why the source reads `[M, σ]_M ∈ B(M)_{K_M}` as "`E` admet des vecteurs fixes
par `K_M` non nul". `StandardRepresentativeFixedVectorCriterionStatement` states the claim in
this second form, which needs no inertial classes of `M`.

## Framework

Everything is published; this module constructs nothing.

- `F` is a nonarchimedean local field of either characteristic and `G` an actual connected
  reductive group scheme over `Spec F` (`hG : IsConnectedReductive G`). `rationalPoints G`
  carries `rationalPointTopology F G.X` and `rationalPoint_isTopologicalGroup F G`.
- `i : S.toGrp ⟶ G` is a maximal split torus (`IsMaximalSplitTorus i`), `ν` a generic
  cocharacter (`IsGenericCocharacter i ν`), and `_hstandard` the existence of a standard
  cocharacter for every `J ⊆ simpleRelativeRoots i ν`. These are the data of the published
  `StandardBernsteinFixedVectorVisibilityStatement` and of the published
  `StandardIwahoriFixedVectorSubquotientGenerationStatement`, copied verbatim.
- For `J ⊆ simpleRelativeRoots i ν` (a `Set (characterLattice S)`), the published
  `standardLeviPoints i ν J`, `standardUnipotentPoints i ν J` and
  `standardOppositeUnipotentPoints i ν J` are `M_J(F)`, `N_J(F)` and `N̄_J(F)` inside `G(F)`.
  For `I : Finset (SimpleRoot i ν)`, `levi i ν I = standardLeviPoints i ν (rootSet i ν I)`.
  `P_∅ = M_∅ N_∅` is the minimal standard parabolic.
- In the last two statements the actual standard family is
  `family := standardBernsteinFamily i ν hG hi hν` (published theorem in
  `StandardBernsteinFixedVectorReduction`), with the `T2Space F`, `LocallyCompactSpace` and
  `NonarchimedeanGroup` instances supplied by the published `BruhatTits.localField_t2Space`,
  `rationalPoint_locallyCompactSpace` and `Plancherel.rationalPoints_nonarchimedeanGroup`,
  exactly as in `StandardBernsteinFixedVectorVisibilityStatement`.
- Cuspidal data are the published `BernsteinCuspidalDatum.{uF, max uF uV} i ν family`: a
  finite set `a.roots` of simple roots (the standard Levi `M_I`, `I = a.roots`), an irreducible
  smooth complex representation `a.representation` of the rational points of the Levi scheme
  `bernsteinLeviScheme i ν I`, cuspidal. `bernsteinLiteralLeviRep i ν I σ` transports it to the
  literal subgroup `levi i ν I` of `G(F)`. `bernsteinInertialClass i ν family a` is the class
  `[a]_G ∈ B(G)`, and `IsBernsteinInertialSupport i ν family s π` says that `π` is irreducible
  and a subquotient of the normalized induction of some datum in the class `s`.

**`B(G)_K`.** For a compact open `K`, the statement "`s ∈ B(G)_K`" is written
`∃ π, IsBernsteinInertialSupport i ν family s π ∧ Nontrivial (fixedVectors π.representation K)`:
some irreducible smooth representation with inertial support `s` has a nonzero `K`-fixed vector.
This is the source's definition above (`B(G)_K` is the set of inertial supports of the members
of `Irr(G)_K`). It is the same set as the set
`{s | ∃ π, IsBernsteinInertialSupport i ν family s π ∧ HasFixed π}` of the published
`CompactOpenInertialFinitenessStatement` (VI.10.6, Theorem): `Nontrivial` of the published
submodule `fixedVectors π.representation K` says that it contains a nonzero vector, which is
`HasFixed π`.

## The hypotheses on `K`

In all three statements the hypotheses on `K₀` and `K` are copied word for word from the
published `StandardIwahoriFixedVectorSubquotientGenerationStatement` (Renard VI.9.4, whose class
of `K` is the class of the VI.10.6 Proposition quoted above):

- `K₀ : Subgroup (rationalPoints G)` is compact (`_hK₀`) and has the Iwasawa decomposition
  `G(F) = M_∅(F) N_∅(F) K₀` (`_hIwasawa`);
- `K : OpenSubgroup (rationalPoints G)` is compact (`_hK`), contained in `K₀` (`_hKK₀`) and
  normalized by `K₀` (`_hnormal : K₀ ≤ Subgroup.normalizer K`), i.e. "inclus et distingué dans
  `K₀`";
- `_hIwahori`: for every `J ⊆ simpleRelativeRoots i ν`, the published
  `HasIwahoriIntersectionDecomposition K M_J N_J N̄_J`, that is, the map
  `(K ∩ N̄_J) × (K ∩ M_J) × (K ∩ N_J) → K`, `(x, y, z) ↦ xyz`, is bijective. This is the
  source's "décomposition d'Iwahori selon les sous-groupes paraboliques standards"; the
  Markdown of the published statement explains the encoding.

Of the source's assumptions on `K₀`, the published statement and these three keep only
compactness and the Iwasawa decomposition.

## `StandardLeviCompactInheritanceStatement`

For `J ⊆ simpleRelativeRoots i ν`, with `M = standardLeviPoints i ν J`, the conclusion is the
conjunction of:

1. `K ∩ M` (as `K.comap M.subtype`, a subgroup of the subtype `M` with the subspace topology)
   is open and compact in `M`;
2. there is a subgroup `K₀M ≤ M` of `G(F)` such that `K₀M` is compact, `M` has the Iwasawa
   decomposition `M = M_∅ (N_∅ ∩ M) K₀M` (every `g ∈ M` is `m n k` with `m ∈ M_∅(F)`,
   `n ∈ N_∅(F) ∩ M`, `k ∈ K₀M`), and `K ∩ M ≤ K₀M ≤ normalizer (K ∩ M)`;
3. for every `I ⊆ J`, `HasIwahoriIntersectionDecomposition (K ∩ M) M_I (N_I ∩ M) (N̄_I ∩ M)`.

These are the properties of `K` "relativement au groupe `M`": the minimal standard parabolic
of `M` is `P_∅ ∩ M = M_∅ (N_∅ ∩ M)`, and the standard parabolics of `M` are
`P_I ∩ M = M_I (N_I ∩ M)`, `I ⊆ J`, with opposite unipotent radical `N̄_I ∩ M`. In 3 the
subgroups are those of `G(F)`, and `(K ∩ M) ∩ M_I = K ∩ M_I` because `M_I ≤ M`.

**Why `K₀M` is existentially quantified.** The source's `K₀` for `M` is `K₀ ∩ M`. Under the
published hypothesis on `K₀` (only the Iwasawa decomposition of `G`), the Iwasawa decomposition
of `M` with respect to `K₀ ∩ M` does not follow from that of `G`. For example, for
`G = GL₃`, `g = 1 + ϖ^{-1}E₁₃` and `K₀ = g GL₃(𝒪) g^{-1}`, one has `G = B K₀` (because
`G = B GL₃(𝒪)` and `g ∈ B`), but a block-diagonal `m = diag(A, c)` lies in `K₀` iff `A ∈ GL₂(𝒪)`, `c ∈ 𝒪^×`,
`A₂₁ ∈ ϖ𝒪` and `A₁₁ ≡ c mod ϖ`. So the `GL₂`-components of `K₀ ∩ M`, `M = GL₂ × GL₁`, lie in
the Iwahori subgroup of `GL₂(𝒪)`, and `M ≠ (B₂ × GL₁)(K₀ ∩ M)`. The statement therefore asserts that
some compact `K₀M` with the source's properties exists. A suitable subgroup always exists:
`K₀M = p_J(K₀ ∩ P_J)`, where `p_J : P_J → M_J` is the Levi projection (see the proof route
below). When `K₀ ∩ P_J = (K₀ ∩ M_J)(K₀ ∩ N_J)`, this is `K₀ ∩ M_J`.

## `StandardRepresentativeFixedVectorCriterionStatement`

For every `a : BernsteinCuspidalDatum.{uF, max uF uV} i ν family` (standard Levi `L = M_I`,
`I = a.roots`, cuspidal `σ = a.representation`):

`[a]_G ∈ B(G)_K` iff
`Nontrivial (fixedVectors (bernsteinLiteralLeviRep i ν I σ).representation (K.comap (levi i ν I).subtype))`,

that is, iff `σ`, on the literal subgroup `L(F) = levi i ν I` of `G(F)`, has a nonzero vector
fixed by `K ∩ L(F)`. This is the source's "`𝔰 ∈ B(G)_K` si et seulement si `E` admet des
vecteurs fixes par `K_M` non nul" for `𝔰 = [M, (σ, E)]_G`, with the source's `M` renamed `L`.
The source states it for a representative whose Levi is standard; here `L` is standard because
all published cuspidal data are standard. Since the left side depends only on the class
`[a]_G`, the statement includes the fact that the right side is the same for all standard
representatives of the class.

## `StandardLeviFixedVectorSupportStatement`

### Cuspidal data and inertial classes of `M`

Let `M = levi i ν J`, `J : Finset (SimpleRoot i ν)`. As in the published
`BernsteinInductionRestrictionStatement`, a standard cuspidal datum of `M` is a published datum
`b` of `G` with `b.roots ⊆ J`; the Levi `M_{b.roots}` is contained in `M`, and normalized
induction inside `M` from it is the published `leviNormalizedInductionFunctor` along the
parabolic `P_{b.roots} ∩ M = M_{b.roots} (N_{b.roots} ∩ M)` of `M` (field
`family.leviDecomposition J I`, indices written as `leviIndex J I` for `I : Finset J`, the
inclusion `M_{b.roots} ≤ M` from the published `levi_le_of_subset` and
`standardLeviIntersection`). Every cuspidal datum of `M` is `M(F)`-conjugate to one whose Levi
is standard in `M`, so these data represent all of `B(M)`.

Two such data `b`, `b'` are *`M`-inertially equivalent* when there is a published
`c : RationalLeviConjugacy (Standard.leviHom i ν (rootSet i ν b.roots))
(Standard.leviHom i ν (rootSet i ν b'.roots))` with `c.point ∈ levi i ν J` and
`IsRationalInertiaRelated (bernsteinLeviScheme i ν b.roots) b.representation
(rationalIsoPullback c.iso b'.representation)`. Without the condition `c.point ∈ levi i ν J`
this is literally the published `IsBernsteinInertiaRelated i ν family b b'` (inertial
equivalence in `G`). With it, the conjugating point lies in `M(F)`: this is Renard's
`[L, σ]_M = [L', σ']_M` (VI.7.1, with `M` in place of `G`). The unramified characters are
those of the Levi `L` itself, so they are the same whether `L` is viewed in `M` or in `G`.

Hence `i_{MG}([b]_M) = [b]_G = bernsteinInertialClass i ν family b`, literally.

### The statement

For every `J` and every datum `b` with `b.roots ⊆ J`, the following are equivalent:

- **`[b]_M ∈ B(M)_{K_M}`:** there is a smooth representation `τ` of `M(F)` (carrier universe
  `max uF uV`) such that `τ` is irreducible, `τ` has a nonzero vector fixed by
  `K ∩ M(F) = K.comap (levi i ν J).subtype`, and for some `I : Finset J` and some datum `b'`
  with `b'.roots = leviIndex J I`, `b'` is `M`-inertially equivalent to `b` and `τ` is a
  subquotient (`SmoothRep.IsSubquotient`) of the normalized induction inside `M` of `b'`
  (that is, `τ` has inertial support `[b]_M` in `M`);
- **`i_{MG}([b]_M) ∈ B(G)_K`:** there is an irreducible smooth representation `π` of `G(F)`
  with `IsBernsteinInertialSupport i ν family [b]_G π` and a nonzero `K`-fixed vector.

The induction term is copied verbatim from the fibre property of the published
`BernsteinInductionRestrictionStatement`.

## Proof routes (not part of the statements)

**Inheritance.** (1) `K ∩ M` is open in `M` because `K` is open; it is compact because `K` is
compact and `M(F)` is closed (published `isClosed_levi_of_isNonarchimedeanLocalField`).
(2) Take `K₀M = p_J(K₀ ∩ P_J)`. It is compact (`P_J(F)` closed, `p_J` continuous). Given
`g ∈ M`, write `g = mnk` by the Iwasawa decomposition of `G`; then
`k = n^{-1}m^{-1}g ∈ K₀ ∩ P_J`, and applying `p_J` gives `g = m p_J(n) p_J(k)` with
`p_J(n) ∈ N_∅ ∩ M`. Also `K ∩ M ≤ K₀M` since `p_J` is the identity on `M`. The Iwahori
decomposition along `P_J` gives `K ∩ P_J = (K ∩ M)(K ∩ N_J)`, hence `p_J(K ∩ P_J) = K ∩ M`;
each `k₀ ∈ K₀ ∩ P_J` normalizes `K` and `P_J`, hence `K ∩ P_J`, so `p_J(k₀)` normalizes
`K ∩ M`. (3) For `k ∈ K ∩ M`, decompose `k = xyz` along `P_I` (`x ∈ K ∩ N̄_I`,
`y ∈ K ∩ M_I`, `z ∈ K ∩ N_I`). Since `I ⊆ J`, `N̄_I = N̄_J (N̄_I ∩ M)` and
`N_I = (N_I ∩ M) N_J`; write `x = x''x'` and `z = z'z''` with `x'' ∈ N̄_J`, `x' ∈ N̄_I ∩ M`,
`z' ∈ N_I ∩ M`, `z'' ∈ N_J`. Then `k = x'' (x'yz') z''` with `x'yz' ∈ M`, and also
`k = 1 · k · 1`; uniqueness in the big cell `N̄_J × M_J × N_J → G` gives `x'' = z'' = 1`, so
`x, z ∈ M`. Uniqueness of the factors is inherited from `K`.

**Representative criterion.** (⇐) If `σ^{K ∩ L} ≠ 0`, then for `V = i_P^G(σ)` the Jacquet
lemma (`V^K → (V_N)^{K ∩ L}` surjective, for `K` with an Iwahori decomposition along `P`) and
the geometric lemma (`σ` is a subquotient of the normalized Jacquet module of `V`; the
modulus character is trivial on `K ∩ L`) give `V^K ≠ 0`. A nonzero `v ∈ V^K` generates a
finitely generated subrepresentation `W`; its image in an irreducible quotient of `W` is a
nonzero `K`-fixed vector, so that quotient `π` is an irreducible subquotient of
`V = i_P^G(σ)` with `π^K ≠ 0`; in particular `π` has inertial support `[a]_G`. (⇒) If `π` has
inertial support `[a]_G` and `π^K ≠ 0`, the second part of the published
`CompactOpenInertialFinitenessStatement` gives an irreducible subquotient `π'` of `i_P^G(σ)` with
`π'^K ≠ 0`, so `i_P^G(σ)^K ≠ 0`. By the Mackey formula (Renard III.2.2),
`i_P^G(σ)^K ≅ ⊕_{P\G/K} σ^{p(K_g)}`, so `σ^{p(K_g)} ≠ 0` for some `g`. Here `p` is the Levi
projection `p_L : P → L`. Writing `g = qk` with `q ∈ P_∅ ≤ P` and `k ∈ K₀` (Iwasawa),
normality of `K` in `K₀` gives `K_g = q(K ∩ P)q^{-1}`, and the Iwahori decomposition gives
`p_L(K ∩ P) = K ∩ L`, so `p_L(K_g) = p_L(q)(K ∩ L)p_L(q)^{-1}` and `σ^{K ∩ L} ≠ 0`.

**Corollary.** (⇐) If `[b]_G ∈ B(G)_K`, the criterion gives `σ^{K ∩ L} ≠ 0`; the Jacquet lemma
and the geometric lemma inside `M`, for `K ∩ M` (which has the Iwahori decomposition by the
inheritance statement), give an irreducible subquotient `τ` of `i^M(σ)` with
`τ^{K ∩ M} ≠ 0`; take `b' = b` and `c = RationalLeviConjugacy.refl`, whose point `1` lies in
`M`. (⇒) If `τ` is as on the left, then `i^M(σ')^{K ∩ M} ≠ 0`; the Mackey argument inside `M`,
with the compact subgroup `K₀M` of the inheritance statement, gives `σ'^{K ∩ L'} ≠ 0`; the
criterion gives `[b']_G ∈ B(G)_K`; and `M`-inertial equivalence implies `G`-inertial
equivalence, so `[b]_G = [b']_G`.

## Not stated here

- The Iwasawa decomposition of `M` with respect to `K₀ ∩ M` itself (see above).
- `B(M)` as a type and the map `i_{MG}` as a function: the statement is phrased through
  representatives, as `BernsteinInductionRestrictionStatement` is. Ledger gap 4 asked for these
  objects; they are not needed for the content of the Corollary.
