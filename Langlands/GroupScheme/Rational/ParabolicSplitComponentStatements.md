# Split components of parabolic subgroups (Renard V.3.1 and V.3.2): statements

Module `Langlands.GroupScheme.Rational.ParabolicSplitComponentStatements`. Namespace
`Langlands.GroupScheme`. Universe parameter `u` (the base field).
The module contains six **statements**, the `Prop`-valued definitions

- `ParabolicSplitComponentLeviStatement`,
- `LeviSplitComponentRadicalStatement`,
- `ParabolicSplitComponentConjugacyStatement`,
- `LeviCentralizerCharacterizationStatement`,
- `MinimalParabolicSplitComponentStatement`,
- their conjunction `ParabolicSplitComponentStatements`.

It proves nothing and introduces no other definition.

Worker 4 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`, with the agreement of Worker 1222. Renard recalls these
facts from Borel–Tits and Springer without proof. The Chapter V item ledger
(`notes/renard/item-ledger-v.md`, V.3.1 and V.3.2 rows) lists the split-component form of V.3.1
for non-minimal Levi subgroups as recalled and not stated.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`. Worker 4 read V.2.1 (printed p.104 /
PDF p.110) and V.3.1–V.3.2 (printed p.110 / PDF p.116).

V.2.1 defines split components for an arbitrary connected linear algebraic group `G`:

> On appelle composante déployée de `G` un tore défini et déployé sur `F`, contenu dans le
> radical `R(G)` et maximal pour cette propriété.

V.3.1 and V.3.2 read:

> Soit `P` un sous-groupe parabolique de `G` et `N` son radical unipotent. […] Les sous-groupes
> de Levi sont obtenus de la manière suivante. Soit `A` une composante déployée de `P` et posons
> `M = Z(G, A)`. Alors `M` est un facteur de Levi de `P`. De plus `A` est la composante déployée
> de `M`. Si l'on se donne `P`, le choix d'une composante déployée de `P` est donc équivalent au
> choix d'un facteur de Levi. Le radical unipotent `N` agit transitivement par conjugaison sur
> l'ensemble des composantes déployées de `P`, et donc sur l'ensemble des facteurs de Levi de
> `P`. Les sous-groupes de Levi `M` de `G` sont les centralisateurs de tores déployés `A` dans
> `G` tels que `A` est la composante déployée de `M`. […]
>
> V.3.2 Les sous-groupes paraboliques minimaux de `G` sont ceux dont les composantes déployées
> sont des tores déployés maximaux de `G`. Deux tores de `G`, déployés et maximaux pour cette
> propriété sont conjugués dans `G`. Deux sous-groupes paraboliques minimaux de `G` sont donc
> conjugués dans `G`.

Section V.3 refers to [7] (A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27, 1965)
and [42] (T. A. Springer, *Linear algebraic groups*, 2nd ed.). Worker 4 did not consult them.

## Already in the Library

The following parts of V.3.1–V.3.2 are published elsewhere and are not restated here.

- Existence of Levi factors and simple transitivity of the unipotent radical on them:
  `ParabolicRadicalTorusLeviStatement`, `ParabolicRadicalTorusCentralizerLeviStatement` and
  `RationalLeviConjugacyStatement`.
- `Z_G(A_M) = M` for a rational Levi `M` with split component `A_M`, `N_G(A_M) = N_G(M)` and the
  finiteness of `P(M)`: `LeviSplitComponentRecallStatements` (Worker 1222).
- The opposite parabolic: `OppositeDynamicParabolicUniquenessStatement`.
- The minimal case of the centralizer description: `MinimalParabolicLeviCentralizerStatement`.
- The second and third sentences of V.3.2: `MaximalSplitTorusConjugacyStatement` and
  `MinimalParabolicConjugacyStatement`.
- Existence and uniqueness of the split component of a connected reductive group:
  `SplitComponentStatement`.

The modules `SplitComponentAmbientMaximality`, `MinimalParabolicSplitComponent`,
`LeviTorusCentralizerConjugacy` and `ParabolicLeviTorusConjugation` are related. They prove
conditional infrastructure, for example maximality of a Levi split component in `G` from
supplied centralizer representations, and do not state the assertions below.

## Published objects used

- `IsConnectedReductive G`, `IsParabolicSubgroup j` for `j : P ⟶ G`, `IsRationalLeviSubgroup l`
  for `l : L ⟶ P`: a connected reductive group over `k`, a parabolic subgroup defined over `k`,
  and a Levi factor of it defined over `k`.
- `IsGeometricSolvableRadical r` for `r : R ⟶ P` ([LeviSubgroup](LeviSubgroup.md)): `R` is the
  radical `R(P)`, over `k` and after base change to an algebraic closure.
- `LeviSubgroup.IsGeometricUnipotentRadical u` for `u : U ⟶ P`: `U` is the unipotent radical
  `N` of `P` in the same sense. It is the predicate used by `RationalLeviConjugacyStatement`.
- `IsSplitSubtorus i` and `IsMaximalSplitTorus i` ([SplitTorus](SplitTorus.md)): a closed
  embedding of a split torus, and one that is maximal among them, maximality being expressed by
  factorizations.
- `IsSplitComponent i` ([Characters](Characters.md)): a central split torus maximal among the
  central split tori. For a connected reductive group this is Renard's split component (V.2.1:
  "une composante déployée de `G` est alors un tore déployé maximal dans le centre de `G`").
- `IsMinimalParabolicSubgroup j` ([MinimalParabolic](MinimalParabolic.md)): minimality among
  rational parabolics, comparing ranges on all test schemes.
- `torusCentralizer i` ([TorusCentralizer](TorusCentralizer.md)) and
  `SubgroupFunctor.IsRepresentedBy`: the centralizer subgroup functor, tested after every
  refinement of the test scheme, and its representation by a monomorphism.
- `GroupScheme.innerIso g` ([InnerAutomorphism](../InnerAutomorphism.md)): conjugation by a
  rational point `g`.

## The statements

Throughout, `k` is a field, `G` a connected reductive group over `k`, `j : P ⟶ G` a parabolic
subgroup and `r : R ⟶ P` its radical. A **split component of `P`** is, following V.2.1, a map
`a : A ⟶ R` from a commutative group scheme with `IsMaximalSplitTorus a`. The source `A` is
the split torus. It is a maximal split torus of `R(P)`, embedded in `P` by `a ≫ r`.

**`ParabolicSplitComponentLeviStatement`** (V.3.1, "Soit `A` une composante déployée de `P`
[…]"). For a split component `a : A ⟶ R` there are a rational Levi factor `l : L ⟶ P` and
`aL : A ⟶ L` with

- `(torusCentralizer (a ≫ r ≫ j)).IsRepresentedBy (l ≫ j)`: `M = Z(G, A)` and it is a Levi
  factor of `P`;
- `aL ≫ l = a ≫ r` and `IsSplitComponent aL`: `A` is the split component of `M`.

**`LeviSplitComponentRadicalStatement`** (V.3.1, "le choix d'une composante déployée de `P` est
donc équivalent au choix d'un facteur de Levi"). For a rational Levi factor `l : L ⟶ P` and its
split component `aL : A ⟶ L` there is `a : A ⟶ R` with `a ≫ r = aL ≫ l` and
`IsMaximalSplitTorus a`: `A_M` is a split component of `P`.

Together with `LeviSplitComponentCentralizerStatement` (`Z_G(A_M) = M`), these two statements
give the equivalence asserted by Renard. The map `A ↦ Z(G, A)` sends split components of `P` to
Levi factors, the map `M ↦ A_M` sends Levi factors to split components, and the two maps are
mutually inverse.

**`ParabolicSplitComponentConjugacyStatement`** (V.3.1, "Le radical unipotent `N` agit
transitivement par conjugaison sur l'ensemble des composantes déployées de `P`"). For the
unipotent radical `u : U ⟶ P` and two split components `a : A ⟶ R`, `a' : A' ⟶ R` there are a
rational point `q` of `U` and an isomorphism `e : A ≅ A'` with

`a ≫ r ≫ (P.innerIso (q ≫ u.hom.hom)).hom = e.hom ≫ a' ≫ r`.

Conjugation by `q` carries the image of `A` in `P` onto the image of `A'`. The consequence for
Levi factors ("et donc sur l'ensemble des facteurs de Levi") is the published
`RationalLeviConjugacyStatement`.

**`LeviCentralizerCharacterizationStatement`** (V.3.1, "Les sous-groupes de Levi `M` de `G`
sont les centralisateurs de tores déployés `A` dans `G` tels que `A` est la composante déployée
de `M`"). For a homomorphism `m : M ⟶ G` the following are equivalent:

- there are a parabolic `p : P ⟶ G` and a rational Levi factor `l : M ⟶ P` with `l ≫ p = m`;
- there are a split subtorus `a : A ⟶ G` and `aM : A ⟶ M` with
  `(torusCentralizer a).IsRepresentedBy m`, `aM ≫ m = a` and `IsSplitComponent aM`.

**`MinimalParabolicSplitComponentStatement`** (V.3.2, first sentence). For a split component
`a : A ⟶ R` of `P`, `IsMinimalParabolicSubgroup j ↔ IsMaximalSplitTorus (a ≫ r ≫ j)`.

**`ParabolicSplitComponentStatements`** is the conjunction of the five.

## Formalization choices

- **Split components of `P`.** The Library predicate `IsSplitComponent` describes split
  components of a connected reductive group, which are central. A split component of the
  non-reductive group `P` is not central in `P`. The statements therefore use V.2.1 literally,
  through a supplied radical `r` and `IsMaximalSplitTorus` in `R`. A split torus of `P` lies in
  `R(P)` exactly when it factors through the closed embedding `r`, so maximality in `R` is
  maximality among split tori of `P` contained in `R(P)`. No new predicate is introduced.
- **Supplied radicals.** The radical `r` and unipotent radical `u` are hypotheses, as in
  `MinimalParabolicLeviCentralizerStatement` and `RationalLeviConjugacyStatement`. Renard
  records that they are defined over `F` (V.3 opening); their existence is not asserted here.
- **Centralizers.** `Z(G, A)` is the centralizer subgroup functor on all test schemes, and
  "`M` is `Z(G, A)`" is representation by the given monomorphism, as in
  `ParabolicRadicalTorusCentralizerLeviStatement`. `IsRepresentedBy` includes that the
  representing map is a monomorphism.
- **Transitivity only.** Renard asserts transitivity of `N` on split components, and this is
  what is stated. The action is in fact simply transitive, because the action on Levi factors
  is (published `RationalLeviConjugacyStatement`). Uniqueness of `q` is not claimed here.
- **Explicit split subtorus in the characterization.** Renard speaks of split tori `A` in `G`.
  The right-hand side therefore requires `IsSplitSubtorus a`, a closed embedding of a split
  torus, even though this also follows from the other conditions.
- **Base field.** The statements are over an arbitrary field, like the published Chapter V
  structure statements. Renard's `F` is a nonarchimedean local field.

## Why the statements are true

Fix a rational Levi factor `M` of `P`, with unipotent radical `N` and split component `A_M`.
Then `R(P) = Z(M)° ⋉ N`.

- `A_M` is a maximal split torus of `R(P)`. It lies in `Z(M)° ⊆ R(P)`. A split torus `S` of
  `R(P)` containing `A_M` commutes with `A_M`, so `S ⊆ Z_G(A_M) ∩ R(P) = M ∩ R(P) = Z(M)°`. Thus
  `S` is a central split torus of `M`, and `S = A_M` by maximality. This is
  `LeviSplitComponentRadicalStatement`.
- `R(P)` is smooth, connected and affine, so its maximal split tori are conjugate under
  `R(P)(k)` (published `SmoothMaximalSplitTorusConjugacyStatement`). Since
  `R(P)(k) = N(k) Z(M)°(k)` and `Z(M)°` centralizes `A_M`, every split component of `P` is
  `n A_M n⁻¹` with `n ∈ N(k)`. This gives `ParabolicSplitComponentConjugacyStatement`.
- For a split component `A = n A_M n⁻¹`, `Z(G, A) = n M n⁻¹`, a Levi factor of `P` whose split
  component is `A`. This gives `ParabolicSplitComponentLeviStatement`.
- In the characterization, a Levi subgroup `M` has `Z_G(A_M) = M`
  (`LeviSplitComponentCentralizerStatement`). Conversely, the centralizer of a split torus `A`
  equals `Z_G(λ)` for a sufficiently general cocharacter `λ` of `A`. That is the Levi factor of
  the dynamic parabolic `P_G(λ)`, with unipotent radical `U_G(λ)`.
- `P` is minimal if and only if `M` is anisotropic modulo its centre, that is, if and only if
  every split torus of `M` lies in `A_M`. A split torus of `G` containing `A_M` lies in
  `Z_G(A_M) = M`, and a maximal split torus of `M` contains the central `A_M`. Hence this holds
  if and only if `A_M` is a maximal split torus of `G`. Since all split components of `P` are
  conjugate, this gives `MinimalParabolicSplitComponentStatement`.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LeviSubgroup` | `IsRationalLeviSubgroup`, `IsGeometricSolvableRadical`, `LeviSubgroup.IsGeometricUnipotentRadical`; `IsParabolicSubgroup` through its import of `Langlands.GroupScheme.Absolute.Borel` |
| `Langlands.GroupScheme.Rational.TorusCentralizer` | `torusCentralizer` |
| `Langlands.GroupScheme.Rational.Characters` | `IsSplitComponent` |
| `Langlands.GroupScheme.Rational.SplitTorus` | `IsSplitSubtorus`, `IsMaximalSplitTorus` |
| `Langlands.GroupScheme.Rational.MinimalParabolic` | `IsMinimalParabolicSubgroup` |
| `Langlands.GroupScheme.InnerAutomorphism` | `GroupScheme.innerIso` |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
