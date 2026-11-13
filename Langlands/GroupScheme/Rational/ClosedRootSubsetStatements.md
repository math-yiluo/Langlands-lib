# Closed, convex, symmetric and unipotent sets of relative roots (Renard V.4.2): statements

Module `Langlands.GroupScheme.Rational.ClosedRootSubsetStatements`. Namespace
`Langlands.GroupScheme`. Universe parameter `u` (the base field).

The module contains the following.

- **Definitions.** `IsClosedRootSubset`, `IsConvexRootSubset`, `IsSymmetricRootSubset`,
  `positiveRootSubset`, `rootClosure`, `IsParabolicRootSubset`, `parabolicRootLevi`,
  `parabolicRootUnipotent`, `standardParabolicRootSubset`, `standardLeviRootSubset`,
  `standardUnipotentRootSubset`, `IsUnipotentRootSubset`, `IsRootReflection`,
  `rootSubsetWeylGroup`, `IsRootSubsetGroup`, `IsRootSubsetUnipotentGroup`,
  `HasReducedPointIntersection` and `IsRelativeRootAmbient`.
- **Proved lemmas.** `isClosedRootSubset_self`, `IsConvexRootSubset.isClosedRootSubset`,
  `subset_rootClosure`, `rootClosure_subset`, `isClosedRootSubset_rootClosure`,
  `positiveRootSubset_relativeRoots`, `positiveRootSubset_indivisibleRoots`,
  `parabolicRootUnipotent_eq_diff`, `IsRootSubsetGroup.range_eq` and
  `IsRootSubsetUnipotentGroup.range_eq`. They are elementary consequences of the definitions.
- **Statements**, all `Prop`-valued definitions: `ConvexRootSubsetHullStatement`,
  `UnipotentRootSubsetCocharacterStatement`, `SymmetricRootSubsetWeylStatement`,
  `StandardParabolicRootTripleStatement`, `RootSubsetGroupExistenceStatement`,
  `StandardParabolicRootSubsetGroupStatement`, `ClosedRootSubsetGroupIntersectionStatement`,
  `ConvexRootSubsetGroupIntersectionStatement`, `UnipotentRootSubsetGroupIntersectionStatement`,
  and their conjunction `ClosedRootSubsetStatements`.

None of the nine statements is proved here.

Worker 4 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`, with
the agreement of Worker 1222. The Chapter V item ledger (`notes/renard/item-ledger-v.md`, V.4.2
rows) lists the general notions of V.4.2 and the proposition citing [7] 3.22 as recalled and not
stated.

## Source and provenance

The main source is David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`.
Worker 4 read V.3.12 (printed p.112 / PDF p.118) and the opening of V.4 together with V.4.2
(printed p.118 / PDF p.124). V.4.2 reads:

> Soit `T` une partie de `Σ_∅`. On dit que `T` est fermée si `(T + T) ∩ Σ_∅ ⊂ T`. On dit que `T`
> est convexe si `T` est l'intersection de `Σ_∅` avec un cône convexe fermé de `𝔞^*`. Une partie
> fermée `T` de `Σ_∅` est dite symétrique si `T = −T`. Dans ce cas, `T` est un système de racines,
> et l'on note `W_T ⊂ W_G` son groupe de Weyl. Une partie fermée `T` de `Σ_∅` est dite unipotente
> si `T ⊂ w · Σ^+_∅` pour un certain `w ∈ W_G`.
>
> Pour toute partie fermée `T` de `Σ_∅`, on note `G(T)` le sous-groupe algébrique de `G` engendré
> par `M_∅` et les `U_γ`, `γ ∈ T`. Si `T` est unipotent, on note `U(T)` le sous-groupe de `G`
> engendré par les `U_γ`, `γ ∈ T`.
>
> Le résultat suivant est démontré dans [7], 3.22.
>
> **Proposition.** Soient `S`, `T` des parties fermées de `Σ_∅`.
> (i) Si `S` et `T` sont convexes, alors `G(S) ∩ G(T) = G(S ∩ T)`.
> (ii) Si `T` est unipotent, alors `G(S) ∩ U(T) = U(S ∩ T)`.
>
> On appelle une partie fermée `𝒫` de `Σ_∅` parabolique si `Σ^+_∅ ⊂ 𝒫`. Dans ce cas, on pose
> `ℳ = 𝒫 ∩ (−𝒫)`, `𝒩 = 𝒫 \ ℳ`, et l'on dit que `(𝒫, ℳ, 𝒩)` est un triplet parabolique dans
> `Σ_∅`.
>
> **Proposition** ([7], 5.12–5.18). Soit `Θ` une partie de `Δ_∅`, et soient `𝒫`, `ℳ` les parties
> fermées de `Σ_∅` engendrées par `Σ^+_∅ ∪ (−Θ)` et `(−Θ) ∪ Θ` respectivement. Alors
> `(𝒫, ℳ, 𝒩 = 𝒫 \ ℳ)` est un triplet parabolique dans `Σ_∅` et `P = MN` est un sous-groupe
> parabolique standard de `G`, où `P = G(𝒫)`, `M = G(ℳ)` et `N = U(𝒩)`. Tout sous-groupe
> parabolique standard `P = MN` de `G` est obtenu ainsi. De plus, la partie `Θ` est uniquement
> déterminée par la donnée de `(𝒫, ℳ, 𝒩)` ou de `P = MN`. En particulier, les parties `𝒫`, `ℳ`
> et `𝒩` sont convexes.

The opening of V.4 defines the root groups: for `γ ∈ Σ_∅`, `U_γ` is the unipotent subgroup
normalized by `A_∅` whose Lie algebra has only the weights `γ` and `2γ`, maximal for this
property. V.3.12 fixes `Σ'_∅ = Σ'(A_∅)`, the set of all roots of `A_∅`, and its reduced subset
`Σ_∅ = Σ(A_∅)` of indivisible roots, with positive roots `Σ^+_∅` and simple roots `Δ_∅`
determined by the minimal parabolic `P_∅`.

[7] is A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), registered as
`borel-tits-1965-groupes-reductifs`. Worker 4 read §3.8 (printed pp.76–77 / PDF pp.23–24),
§§3.21–3.23 (printed pp.83–84 / PDF pp.30–31) and §§5.12–5.18 (printed pp.99–101 /
PDF pp.46–48). Proposition 3.22 reads:

> Soient `S` un tore de `G` et `ψ`, `η` deux parties quasi-closes de `Φ(S, G)`. Alors :
> a) `S_ψ ∩ S_η = S_{ψ∩η}` […].
> b) Si `ψ ∩ η` est convexe, `G_ψ ∩ G_η = G_{ψ∩η}`.
> c) Si `ψ` est unipotent, `U_ψ ∩ G_η = U_ψ ∩ U_η = U_{ψ∩η}`.

In §3.8, `Φ(S, G)` is the set of all roots of `S`, so it is possibly nonreduced. Every closed
subset is quasi-closed. `G_ψ` is the subgroup generated by `Z(S)` and the root groups `U_a`
(`a ∈ ψ`). For a maximal split torus `S` (3.8 (iv)), a quasi-closed subset is unipotent exactly
when it consists of positive roots for some ordering. Borel–Tits call a set convex when it is the
intersection of `Φ(S, G)` with a convex cone, not necessarily closed. Since a set of roots is
finite and the cone spanned by a finite set is closed, this is the same as Renard's notion. The
proofs of 3.22 b) and c) reduce to an algebraically closed field, and the groups there are
varieties, that is reduced.

Worker 4 also read §5 of the 1972 *Compléments* (`borel-tits-1972-complements-groupes-reductifs`,
printed pp.274–275 / PDF pp.23–24), which corrects the 1965 article. (5.1) replaces the second
equality (2) of 3.8 by an inclusion. It concerns intermediate tori, which are not used here. (5.2)
extends 5.7 to arbitrary subsets, for use in the proof of 5.8, without changing 5.8. (5.5)
corrects misprints, among them `Φ(S, G)` for `Φ(S, T)` in 3.8 (p.76), and updates the references
to Bourbaki, among them those in the proofs of 3.21 b) and 5.14. None of these changes the
statements of 3.8, 3.21–3.22 or 5.12–5.18 used here.

The nine statements combine sentences of V.4.2 with the Borel–Tits results Renard cites, and two
of them are reformulations that the formalization needs (see *Provenance of each statement*).

## Setting and published objects used

Throughout, `k` is a field, `G` a connected reductive group over `k` (`IsConnectedReductive G`)
and `i : T ⟶ G` a maximal split torus (`IsMaximalSplitTorus i`), Renard's `A_∅`.

- `relativeRoots i` is Borel–Tits' `Φ(S, G)`, Renard's `Σ'_∅`: the nonzero characters with a
  nonzero weight space in the Lie algebra. It may be nonreduced.
- `RelativeRoot.indivisibleRoots i` (module `RootProductStatement`) is Renard's reduced `Σ_∅`:
  the roots that are not a multiple `m • b`, `m ≥ 2`, of another root.
- A cocharacter `ν` with `IsGenericCocharacter i ν` (nonzero on every root) determines the
  minimal parabolic. `positiveRelativeRoots i ν` and `simpleRelativeRoots i ν`
  ([StandardParabolic](StandardParabolic.md)) are Renard's `Σ^+_∅` (in `Σ'_∅`) and `Δ_∅`. A
  simple root is never divisible, so `Δ_∅` is the same for both ambient sets.
- `relativeWeylGroup i = N(k)/Z(k)` is Renard's `W_G`. `relativeWeylCharacterAction i` is its
  action on the character lattice.
- `RelativeRoot.subgroup i γ` ([RootSubgroup](RootSubgroup.md)) is the root subgroup functor
  `U_γ` on all test schemes. It is the Library's construction of Kaletha–Prasad, whose root group
  has Lie weights `γ` and `2γ`, as in Renard.
- `torusCentralizer i` is the centralizer subgroup functor `Z_G(A_∅) = M_∅`.
- `standardParabolic i ν Θ`, `standardLevi i ν Θ`, `standardUnipotent i ν Θ` and
  `standardRelativeWeylGroup i ν Θ` are the published `P_Θ`, `M_Θ`, `N_Θ` and the relative Weyl
  group of `M_Θ`.
- `RealTorusSpace.Vstar T = ℝ ⊗ X^*(T)` is Renard's `𝔞^*`, and characters are sent to it by
  `χ ↦ 1 ⊗ χ`.
- `IsClosedSubgroup h` means a closed immersion and `IsUnipotent H` the representation-theoretic
  unipotence of [Reductive/Basic](../Reductive/Basic.md).

## Definitions

The combinatorial notions take the ambient root set `R` as an explicit parameter, so that both
Renard's `Σ_∅` and Borel–Tits' `Φ(S, G)` can be used.

- `IsClosedRootSubset R X`: `X ⊆ R` and `β + γ ∈ X` whenever `β, γ ∈ X` and `β + γ ∈ R`. The case
  `β = γ` is included, as in `(T + T) ∩ Σ_∅ ⊂ T`.
- `IsConvexRootSubset R X`: there is a closed pointed cone `C ⊆ 𝔞^*` with
  `X = {γ ∈ R | 1 ⊗ γ ∈ C}`. A pointed cone is a convex cone containing `0`, which a nonempty
  closed convex cone always does. `𝔞^*` carries its canonical module topology.
- `IsSymmetricRootSubset R X`: `X` is closed and `X = −X`.
- `positiveRootSubset R ν`: the elements of `R` pairing positively with `ν`. It is
  `positiveRelativeRoots i ν` for `R = relativeRoots i` and
  `RelativeRoot.indivisiblePositiveRoots i ν` for `R = RelativeRoot.indivisibleRoots i`
  (lemmas `positiveRootSubset_relativeRoots` and `positiveRootSubset_indivisibleRoots`).
- `rootClosure R X`: the intersection of the closed subsets of `R` containing `X`, that is, the
  closed subset generated by `X`. It is closed when `X ⊆ R` (`isClosedRootSubset_rootClosure`).
- `IsParabolicRootSubset R ν P`: `P` is closed and contains `positiveRootSubset R ν`.
  `parabolicRootLevi P = P ∩ (−P)` and `parabolicRootUnipotent P = P \ (P ∩ (−P))` are `ℳ` and `𝒩`
  (`parabolicRootUnipotent_eq_diff`).
- `standardParabolicRootSubset R ν Θ` and `standardLeviRootSubset R Θ` are the closed subsets
  generated by `Σ^+_∅ ∪ (−Θ)` and `Θ ∪ (−Θ)`. `standardUnipotentRootSubset R ν Θ` is the
  corresponding `𝒩`.
- `IsUnipotentRootSubset i ν R X`: `X` is closed in `R` and `X ⊆ w · positiveRootSubset R ν` for
  some `w ∈ W_G`.
- `IsRootReflection i w β`: there is a cocharacter `c` with `⟨β, c⟩ = 2` and
  `w χ = χ − ⟨χ, c⟩ β` for every character `χ`. Since the action of `W_G` on characters is
  faithful, `w` is the reflection `s_β`. The coroot `c` is integral.
- `rootSubsetWeylGroup i X`: the subgroup of `W_G` generated by the elements acting as
  reflections with roots in `X`. For symmetric `X` this is Renard's `W_X ⊂ W_G`.
- `IsRootSubsetGroup i X h`, for `h : H ⟶ G`: `h` is a closed subgroup whose range contains
  `torusCentralizer i` and every `RelativeRoot.subgroup i γ` (`γ ∈ X`) on every test scheme, and
  whose range is contained in the range of every closed subgroup with these two properties. This
  is "le sous-groupe algébrique de `G` engendré par `M_∅` et les `U_γ`": the smallest closed
  subgroup containing them. `IsRootSubsetGroup.range_eq` proves that it is unique as a subgroup
  functor.
- `IsRootSubsetUnipotentGroup i X h`: the same without `M_∅`, Renard's `U(X)`, with
  uniqueness `IsRootSubsetUnipotentGroup.range_eq`.
- `HasReducedPointIntersection h₁ h₂ h₃`: on every test scheme `U` over `k` whose underlying
  scheme is reduced, a point `g : U ⟶ G` lies in the ranges of `h₁` and `h₂` exactly when it lies
  in the range of `h₃`. When `h₃` is a closed subgroup with reduced source, this says exactly that
  the reduced closed subscheme underlying the scheme-theoretic intersection `H₁ ∩ H₂` is `H₃`.
  This is the meaning of the intersections of [7], which are intersections of varieties.
- `IsRelativeRootAmbient i R`: `R` is `relativeRoots i` or `RelativeRoot.indivisibleRoots i`.

## The statements

All statements quantify over `k`, a connected reductive `G` and a maximal split torus `i`.
Where the minimal parabolic matters, they also quantify over a generic cocharacter `ν`. "In
either ambient set" means for every `R` with `IsRelativeRootAmbient i R`.

**`ConvexRootSubsetHullStatement`.** In either ambient set, `X` is convex if and only if `X ⊆ R`
and every root of `R` in the cone spanned by `X` (`PointedCone.hull ℝ`) lies in `X`.

**`UnipotentRootSubsetCocharacterStatement`.** In either ambient set, `X` is unipotent if and
only if it is closed and some cocharacter `ζ` pairs positively with every element of `X`.

**`SymmetricRootSubsetWeylStatement`** (V.4.2, "`T` est un système de racines, et l'on note
`W_T ⊂ W_G` son groupe de Weyl"). In either ambient set, let `X` be symmetric. Then every
`β ∈ X` has a reflection `w ∈ W_G`, every reflection with root in `X` maps `X` onto `X`, and
every element of `W_X` maps `X` onto `X`.

**`StandardParabolicRootTripleStatement`** (V.4.2, combinatorial part of the proposition citing
[7] 5.12–5.18). In either ambient set, let `Θ ⊆ Δ_∅` and let `𝒫`, `ℳ`, `𝒩` be the standard
subsets. Then:

- `𝒫` is parabolic;
- `𝒫 ∩ (−𝒫) = ℳ`, so `(𝒫, ℳ, 𝒩)` is the parabolic triple of `𝒫`;
- `𝒫 = {γ ∈ R | ⟨γ, ν⟩ > 0 or γ ∈ ℤΘ}`, where `ℤΘ` is `AddSubgroup.closure Θ`;
- `ℳ = {γ ∈ R | γ ∈ ℤΘ}`;
- `𝒫`, `ℳ` and `𝒩` are convex, `𝒩` is unipotent and `ℳ` is symmetric;
- `Θ = {α ∈ Δ_∅ | −α ∈ 𝒫}`, so `Θ` is determined by `(𝒫, ℳ, 𝒩)`.

**`RootSubsetGroupExistenceStatement`** (V.4.2, "on note `G(T)`", "on note `U(T)`"). For every
`X ⊆ relativeRoots i` there are `h : H ⟶ G` with `IsRootSubsetGroup i X h` and
`h' : H' ⟶ G` with `IsRootSubsetUnipotentGroup i X h'`, with `H` and `H'` smooth, affine and
connected. Moreover, in either ambient set, every `U(X)` is unipotent when `X` is unipotent.

**`StandardParabolicRootSubsetGroupStatement`** (V.4.2, group part of the proposition citing
[7] 5.12–5.18). In either ambient set, for `Θ ⊆ Δ_∅`, every `G(𝒫)` has range
`standardParabolic i ν Θ`, every `G(ℳ)` has range `standardLevi i ν Θ`, every `U(𝒩)` has range
`standardUnipotent i ν Θ`, and `W_ℳ` is `standardRelativeWeylGroup i ν Θ`, the relative Weyl
group of `M_Θ`.

**`ClosedRootSubsetGroupIntersectionStatement`** ([7] 3.22 b)). In `relativeRoots i`, for closed
`S` and `X` with `S ∩ X` convex, `G(S) ∩ G(X) = G(S ∩ X)` on reduced points
(`HasReducedPointIntersection`).

**`ConvexRootSubsetGroupIntersectionStatement`** (V.4.2 (i), in Renard's reduced `Σ_∅`). For
convex `S` and `X` in `RelativeRoot.indivisibleRoots i`, `G(S) ∩ G(X) = G(S ∩ X)` on reduced
points.

**`UnipotentRootSubsetGroupIntersectionStatement`** (V.4.2 (ii), in the form of [7] 3.22 c)). In
`relativeRoots i`, for closed `S` and unipotent `X`, `G(S) ∩ U(X) = U(S ∩ X)` on reduced points.

**`ClosedRootSubsetStatements`** is the conjunction of the nine.

The intersection statements are about any given `G(S)`, `G(X)`, `U(X)`. Their existence is
`RootSubsetGroupExistenceStatement`, and by the uniqueness lemmas the choice does not matter.

## Provenance of each statement

- `SymmetricRootSubsetWeylStatement`, `StandardParabolicRootTripleStatement`,
  `StandardParabolicRootSubsetGroupStatement` and `ConvexRootSubsetGroupIntersectionStatement`
  state sentences of V.4.2.
- `UnipotentRootSubsetGroupIntersectionStatement` and
  `ClosedRootSubsetGroupIntersectionStatement` state [7] 3.22 c) and b) for a maximal split torus,
  which Renard cites for (ii) and (i). The first is V.4.2 (ii) in the nonreduced ambient set; see
  *Source issues*. The second contains V.4.2 (i) in the nonreduced ambient set, because an
  intersection of convex sets is convex and a convex set is closed.
- `RootSubsetGroupExistenceStatement` records that the groups named in V.4.2 exist, and that
  `U(T)` is unipotent, as its notation presupposes.
- `ConvexRootSubsetHullStatement` and `UnipotentRootSubsetCocharacterStatement` are derived
  reformulations. The first makes Renard's existential definition of convexity checkable. The
  second relates Renard's definition of unipotence to that of [7] 3.8 (iv) ("positive for some
  ordering"). Both make the cited Borel–Tits statements comparable with Renard's definitions.

The parts "Tout sous-groupe parabolique standard `P = MN` de `G` est obtenu ainsi" and "`Θ` est
uniquement déterminée par […] `P = MN`" are published. In the Library, the standard parabolics
are the `standardParabolic i ν Θ` with `Θ ⊆ Δ_∅`. The published `StandardParabolicOrderStatement`
proves that `Θ ↦ standardParabolic i ν Θ` is injective. `StandardParabolicClassificationStatement`
proves that every rational dynamic parabolic containing the minimal one is standard. The
determination of `Θ` by the triple is the last conjunct of `StandardParabolicRootTripleStatement`.

## Source issues

- **The reduced reading of (ii) is false.** In V.4.2 the parts `S`, `T` are closed in the reduced
  set `Σ_∅`. Closedness in `Σ_∅` does not imply closedness in `Φ(S, G)`, which is the hypothesis
  of [7] 3.22. Take a quasi-split special unitary group in five variables. Its relative root
  system is of type `BC₂`, with `Φ = {±e₁, ±e₂, ±2e₁, ±2e₂, ±e₁ ± e₂}` and
  `Σ_∅ = {±e₁, ±e₂, ±e₁ ± e₂}`. Let `S = {e₁}` and `T = {e₁ − e₂, e₁ + e₂}`. Both are closed in
  `Σ_∅`, because `2e₁ ∉ Σ_∅`, and `T` is unipotent, because it consists of positive roots. The
  commutator of `U_{e₁−e₂}` and `U_{e₁+e₂}` is a nontrivial subgroup of `U_{2e₁}`. On absolute
  roots this is the nonzero bracket of root spaces `𝔤_{ε₁−ε₂} × 𝔤_{ε₂−ε₅} → 𝔤_{ε₁−ε₅}`. Hence
  `U(T)` contains `U_{2e₁}`, which lies in `U_{e₁} ⊆ G(S)`, while `U(S ∩ T) = U(∅)` is trivial.
  The statement is therefore made in `Φ(S, G)`, where `T` is not closed because
  `(e₁ − e₂) + (e₁ + e₂) = 2e₁`. This is exactly the form of [7] 3.22 c). The same example shows
  that [7] 3.22 b) fails for sets that are only closed in `Σ_∅`: `S ∩ T = ∅` is convex, but
  `G(S) ∩ G(T)` contains `U_{2e₁}` while `G(∅) = M_∅`. So
  `ClosedRootSubsetGroupIntersectionStatement` is stated in `Φ(S, G)` only.
- **The reduced reading of (i) is true.** If `S = Σ_∅ ∩ C` with `C` a closed convex cone, then
  `Φ ∩ C = S ∪ (2S ∩ Φ)`, and `G(S)` is Borel–Tits' `G_{Φ∩C}`, because `U_γ` contains `U_{2γ}`.
  So (i) in `Σ_∅` follows from [7] 3.22 b) applied to `Φ ∩ C₁` and `Φ ∩ C₂`. It is stated
  separately as `ConvexRootSubsetGroupIntersectionStatement`.
- **Intersections.** The groups of [7] are reduced. Scheme-theoretic intersections of smooth
  subgroups need not be reduced, so equality is asserted on reduced test schemes only. Worker 1222
  asked to keep this distinction from scheme-theoretic intersection.

## Formalization choices

- **Two ambient sets.** Renard states V.4.2 in the reduced `Σ_∅`, and [7] in the possibly
  nonreduced `Φ(S, G)`. Every statement whose two readings are both true is made for both, through
  `IsRelativeRootAmbient`. The group intersection statements use the ambient set in which [7]
  proves them, plus the reduced reading of (i).
- **Generated subgroups.** "Sous-groupe algébrique engendré" is encoded as a minimality property
  of a given closed subgroup, compared with all closed subgroups through their subgroup functors
  on all test schemes. The root groups enter through the Library functors
  `RelativeRoot.subgroup i γ`, which are not asserted to be representable here. Existence is a
  separate statement.
- **Unrestricted domains.** `G(X)` and `U(X)` are defined for every set of characters, not only
  for closed or unipotent ones. Renard's restrictions only matter in the statements, which keep
  them.
- **Root system of a symmetric set.** "`T` est un système de racines" is stated as the existence
  of integral reflections in `W_G` for the roots of `X` that preserve `X`. `X` is a finite set of
  nonzero vectors, so these are the root system axioms in the span of `X`. No Mathlib
  `RootPairing` is constructed.
- **Minimal parabolic.** Renard fixes `P_∅`. Here `Σ^+_∅` is given by a generic cocharacter `ν`,
  the standard parabolics being the published `standardParabolic i ν Θ`.
- **Base field.** The statements are over an arbitrary field, like the published Chapter V
  structure statements. Renard's `F` is a nonarchimedean local field.

## Why the statements are true

Let `Φ` be the ambient set. In both cases it is a root system in its span, with Weyl group `W_G`
([7] 5.3 and 5.8, and the published `RelativeRootReflectionExistenceStatement` for integral
coroots), positive system `Σ^+(ν)` and basis `Δ_∅`.

- **Hull.** If `X = Φ ∩ C`, the cone spanned by `X` is contained in `C`. Conversely, `X` is finite,
  so the cone it spans is closed and can be taken as `C`.
- **Cocharacter criterion.** If `X ⊆ wΣ^+(ν)`, take `ζ = w · ν`. Conversely, perturb `ζ` to a
  generic cocharacter that is still positive on the finite set `X`. Its positive roots form a
  positive system, which is `wΣ^+(ν)` for some `w` because `W_G` acts transitively on positive
  systems.
- **Symmetric sets.** For `β, γ ∈ X` with `γ` not proportional to `β`, the `β`-string through `γ`
  in `Φ` is unbroken. `s_β γ = γ − ⟨γ, β^∨⟩ β` is reached from `γ` by repeatedly adding `−β` or
  `β`, which stay in `X` by closedness. If `γ` is proportional to `β`, then `s_β γ = −γ ∈ X`.
- **Standard triple.** Let `𝒫'` be the right-hand side. It is closed, because a root with a
  positive coefficient on a simple root outside `Θ` is positive. A positive root in `ℤΘ` is a sum
  of elements of `Θ` whose partial sums are roots, so its negative lies in the closure of `−Θ`.
  Hence `𝒫 = 𝒫'`, and similarly `ℳ = Φ ∩ ℤΘ`. For a cocharacter `ζ` that vanishes on `Θ` and is
  positive on `Δ_∅ \ Θ`, `𝒫 = {⟨·, ζ⟩ ≥ 0}` and `ℳ = {⟨·, ζ⟩ = 0}` are convex, and
  `𝒩 = {⟨·, ζ⟩ > 0}` is the intersection of `Φ` with the cone it spans. `𝒩 ⊆ Σ^+(ν)`, and the
  simple roots are linearly independent, which gives the recovery of `Θ`.
- **Existence.** The subgroup generated by a family of smooth connected closed subgroups is
  smooth and connected. It is the image of a product map, so every closed subgroup scheme
  containing the family contains it. If `X ⊆ wΣ^+(ν)`, then `U(X)` lies in the unipotent group
  `w U_{P_∅} w⁻¹`.
- **Standard groups.** In [7] 5.12 the standard parabolic `P_Θ`, its Levi `Z_Θ` and its
  unipotent radical `V_Θ` are, in the notation of 3.8, `G_ψ`, `Z(S_Θ)` and `U_{ψ \ (−ψ)}` for
  `ψ = 𝒫` in `Φ(S, G)`, and `Z(S_Θ) = G_{ψ ∩ (−ψ)}` by 3.8. So they are generated by `M_∅` and
  the `U_γ` for `γ` in `𝒫`, `ℳ` or `𝒩`, the last one without `M_∅`
  (each `U_γ` contains `U_{2γ}`, so the reduced ambient set gives the same groups). The published
  `standardParabolic`, `standardLevi` and `standardUnipotent` are the dynamic subgroups of a
  cocharacter vanishing on `Θ` and positive on `Δ_∅ \ Θ`, which are these groups. By [7] 5.17 the
  relative Weyl group of `M_Θ` is generated by the simple reflections `s_α`, `α ∈ Θ`. These also
  generate the Weyl group of the root system `ℳ = Φ ∩ ℤΘ`, with basis `Θ`.
- **Intersections.** These are [7] 3.22 b), c) and the reduction of (i) explained above. The
  points of `H₁ ∩ H₂` with values in a reduced scheme factor through `(H₁ ∩ H₂)_red`. Its
  underlying set is that of `H₃`, as one checks over an algebraic closure. Since `H₃` is closed,
  such points lie in `H₃`. The converse is the minimality of `H₁` and `H₂`.

## Remaining obligations

The proofs of the nine statements are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.StandardParabolic` | `positiveRelativeRoots`, `simpleRelativeRoots`, `standardParabolic`, `standardLevi`, `standardUnipotent`, `standardRelativeWeylGroup`; through its imports `relativeRoots`, `IsGenericCocharacter`, `torusCentralizer`, `relativeWeylGroup` and `latticePairing` |
| `Langlands.GroupScheme.Rational.RootSubgroup` | `RelativeRoot.subgroup` |
| `Langlands.GroupScheme.Rational.RootProductStatement` | `RelativeRoot.indivisibleRoots`, `RelativeRoot.indivisiblePositiveRoots` |
| `Langlands.GroupScheme.Rational.RelativeWeylCharacterAction` | `relativeWeylCharacterAction` |
| `Langlands.GroupScheme.Rational.SplitTorus` | `IsMaximalSplitTorus` |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive`, `IsClosedSubgroup`, `IsUnipotent` |
| `Langlands.Geometry.Building.RealTorusSpace` | `RealTorusSpace.Vstar` |
| `Mathlib.Geometry.Convex.Cone.Pointed` | `PointedCone`, `PointedCone.hull` |
| `Mathlib.Topology.Algebra.Module.ModuleTopology` | `moduleTopology` |
