# Levi subgroups, split components and `P(M)` (Renard V.3.1 and V.3.5, recalled): statements

Module `Langlands.GroupScheme.Rational.LeviSplitComponentRecallStatements`. Namespace
`Langlands.GroupScheme`. Universe parameter `u` (the base field).
The module contains four **statements**, the `Prop`-valued definitions
`LeviSplitComponentCentralizerStatement`, `LeviSplitComponentNormalizerStatement`,
`LeviParabolicFiniteStatement` and their conjunction `LeviSplitComponentRecallStatements`. It
proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Renard recalls these facts from Borel–Tits and
Springer without proof. The Chapter V item ledger lists them as recalled assertions not stated
in the Library.

The Library has related statements:

- the minimal case `MinimalParabolicLeviCentralizerStatement`;
- the centralizer of a maximal torus of the radical, `ParabolicRadicalTorusCentralizerLeviStatement`;
- the finiteness and faithfulness of `N_G(M)/M` (`RP.LeviNormalizerWeylGroupStatements`);
- the bound for maximal Levis, `MaximalLeviParabolicCountStatement` (at most two parabolics).

No published statement gives `Z_G(A_M) = M` or `N_G(A_M) = N_G(M)` for an arbitrary Levi, or the
finiteness of `P(M)`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.3, V.3.1 and V.3.5, printed pp.109–111 / PDF pp.115–117:

> Nous renvoyons le lecteur à [7] ou [42] pour la démonstration des résultats énoncés dans
> cette section. Soit `G` un groupe algébrique connexe, réductif, défini sur `F` et posons
> `G = G(F)`. […] On dira « `P` est un sous-groupe parabolique de `G` » pour exprimer le fait que
> `P` est le groupe des `F`-points d'un sous-groupe parabolique `P` de `G` défini sur `F`. On fera
> de même pour d'autres sous-groupes de `G` définis sur `F`.
>
> V.3.1 […] Soit `A` une composante déployée de `P` et posons `M = Z(G, A)`. Alors `M` est un
> facteur de Levi de `P`. De plus `A` est la composante déployée de `M`. […] Les sous-groupes de
> Levi `M` de `G` sont les centralisateurs de tores déployés `A` dans `G` tels que `A` est la
> composante déployée de `M`. […] Si `M` est un sous-groupe de Levi de `G`, on note `P(M)`
> l'ensemble des sous-groupes paraboliques de `G` admettant `M` comme facteur de Levi. C'est un
> ensemble fini.
>
> V.3.5 Soient `P = MN` un sous-groupe parabolique de `G`, et `A` la composante déployée de `M`.
> Le groupe de Weyl (V.3.5.1) `W(A) = N_G(A)/Z_G(A) = N_G(A)/M = N_G(M)/M` […]

[7] is A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965). [42] is T. A.
Springer, *Linear algebraic groups*, 2nd ed. Worker 1222 did not consult them.

## Published objects used

- `IsConnectedReductive`, `IsParabolicSubgroup j` and `IsRationalLeviSubgroup l` for
  `l : L ⟶ P`, `j : P ⟶ G`: a connected reductive group over `k`, a parabolic subgroup defined
  over `k`, and a Levi factor of it defined over `k`.
- `IsSplitComponent a` for `a : A ⟶ L` ([Characters](Characters.md)): `A` is the split component
  `A_M` of `L`, a central split torus that is maximal among central split tori (Renard's
  *composante déployée*, V.2.1).
- `torusCentralizer i` ([TorusCentralizer](TorusCentralizer.md)) and
  `SubgroupFunctor.normalizer`, `torusNormalizer i` ([TorusNormalizer](TorusNormalizer.md)): the
  centralizer and normalizer subgroup functors, tested after every refinement of the test
  scheme. `SubgroupFunctor.range f` is the subgroup functor of points coming from `f`. Rational
  points are the points over `Over.mk (𝟙 _)` (that is, over `Spec k`).

## The statements

Let `k` be a field, `G` a connected reductive group over `k`, `j : P ⟶ G` a parabolic subgroup,
`l : L ⟶ P` a rational Levi factor (Renard's `M`), and `a : A ⟶ L` a split component of `L`
(Renard's `A_M`).

**`LeviSplitComponentCentralizerStatement`.** `torusCentralizer (a ≫ l ≫ j)` equals
`SubgroupFunctor.range (l ≫ j)`: `Z_G(A_M) = M`. This is also the V.3.1 sentence
`M = Z(G, A)` for the split component `A = A_M`.

**`LeviSplitComponentNormalizerStatement`.** On rational points, the normalizer of `A_M` equals
the normalizer of `M`: `N_G(A_M) = N_G(M)` in `G = G(F)`.

**`LeviParabolicFiniteStatement.`** There is `N` such that every finite family
`q i : Q i ⟶ G` (`i < n`) of parabolic subgroups with rational Levi factors `lQ i : M ⟶ Q i`
satisfying `lQ i ≫ q i = l ≫ p` (the same embedded `M`), with pairwise distinct images, has
`n ≤ N`. So `P(M)` is finite.

**`LeviSplitComponentRecallStatements`** is the conjunction of the three.

## Formalization choices

- **Rational points for the normalizers.** Renard's `N_G(A)` and `N_G(M)` are subgroups of
  `G = G(F)` ("On fera de même pour d'autres sous-groupes"). The normalizer statement is stated
  on rational points. As group schemes the two normalizers can differ. Take
  `G = Res_{K/k} GL₂`, `M` the Weil restriction of the diagonal torus and `A_M` its diagonal
  split part. Over `k̄`, the element `(w, 1)` of `GL₂ × GL₂` normalizes `M` but moves `A_M`.
  The centralizer statement holds scheme-theoretically and is stated as an equality of subgroup
  functors, as in the published minimal case.
- **`P(M)` as a bound.** As in `MaximalLeviParabolicCountStatement`, parabolic subgroups with
  Levi factor `M` are given by inclusions `q i` with rational Levi factors through the same
  embedded `M`, and distinctness is distinctness of the images. Finiteness is the existence of a
  uniform bound on such families.
- **Base field.** The statements are over an arbitrary field, like the published Chapter V
  structure statements. Renard's `F` is a nonarchimedean local field.

## Why the statements are true

`A_M` is central in `M`, so `M ⊆ Z_G(A_M)`. By the structure theory of [7] and [42], the Levi
`k`-subgroups of `P` are exactly the centralizers of the maximal `k`-split tori of the
radical of `P`, which are the split components. So `Z_G(A_M) = M` on `k̄`-points. Centralizers
of tori are smooth, so the equality holds as group schemes, and hence as subgroup functors.

A rational point normalizing `A_M` normalizes `Z_G(A_M) = M`. Conversely, a rational point `g`
normalizing `M` induces a `k`-automorphism of `M`. That automorphism maps `A_M` to a central
split torus, which by maximality is `A_M`.

`P(M)` is in bijection with the set of parabolic subsets of the finite relative root system
`Σ(A_M)` determined by chambers of `𝔞_M` ([7]), hence finite.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.LeviSubgroup` | `IsParabolicSubgroup`, `IsRationalLeviSubgroup` |
| `Langlands.GroupScheme.Rational.TorusCentralizer` | `torusCentralizer` |
| `Langlands.GroupScheme.Rational.TorusNormalizer` | `torusNormalizer`, `SubgroupFunctor.normalizer` |
| `Langlands.GroupScheme.Rational.Characters` | `IsSplitComponent` |
| `Langlands.GroupScheme.Reductive.Basic` | `IsConnectedReductive` |
