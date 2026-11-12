# Minimal representatives of standard Weyl double cosets (Renard V.4.6, Lemma): statement

Module `Langlands.GroupScheme.Rational.StandardWeylMinimalRepresentativesStatement`.
Namespace `Langlands.GroupScheme`. Universe parameter `u`.
The module contains one **statement**, the `Prop`-valued definition
`StandardWeylMinimalRepresentativesStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.4.3–V.4.6, printed pp.119–121 / PDF pp.125–127. For standard
parabolic subgroups `P = MN` and `Q = LU`, Renard sets

> (V.4.6.1) `W^{L,M} = {w ∈ W_G | w·(L ∩ P_∅) ⊂ P_∅, w⁻¹·(M ∩ P_∅) ⊂ P_∅}`

and states:

> **Lemme.** (i) Dans chaque double classe `W_M \ W_G / W_L`, il existe un unique
> élément de `W^{L,M}`. C'est l'élément dont la longueur est minimale dans cette
> double classe. (ii) Si `w ∈ W^{L,M}`, alors `M ∩ w·Q` est un sous-groupe
> parabolique standard de `M`, de facteur de Levi `M ∩ w·L` et de radical
> unipotent `M ∩ w·U` et `w⁻¹·P ∩ L` est un sous-groupe parabolique standard de
> `L`, de facteur de Levi `w⁻¹·M ∩ L` et de radical unipotent `w⁻¹·N ∩ L`. On a
> aussi les décompositions `P ∩ w·Q = (P ∩ w·L)(P ∩ w·U)`,
> `Q ∩ w⁻¹·P = (Q ∩ w⁻¹·M)(Q ∩ w⁻¹·N)`, `N ∩ w·Q = (N ∩ w·L)(N ∩ w·U)`,
> `U ∩ w⁻¹·P = (U ∩ w⁻¹·M)(U ∩ w⁻¹·N)`. (iii)
> `W^{L,M} ∩ W(L, M) ≃ W_M \ W(L, M)/W_L ≃ W(L, M)/W_L`.

Here `W_G = N_G(A_∅)/Z_G(A_∅)`, `W_M = N_M(A_∅)/Z_M(A_∅) ⊆ W_G` (V.4.3.1),
`w·H = gHg⁻¹` for a lift `g` of `w` (V.4.3), and
`W(L, M) = {w ∈ W_G | w·L = M}` (V.4.3.2). The length is the Coxeter length for
the simple reflections of `Δ_∅`.

The operator approved resuming this unit on 11 November 2026, on the actual
algebraic-group objects of the framework and with no separate Weyl data.

## The statement

The setting is that of the published `HasRelativeWeylCoxeterSystem` and
`RationalPointFamily` interfaces. `k` is a nonarchimedean local field, `G` a
connected reductive group scheme over `k`, `i : T.toGrp ⟶ G` a maximal split torus
and `ν` a generic cocharacter. The objects are the published ones:

| Renard | Lean |
| --- | --- |
| `W_G = N(k)/Z(k)` | `relativeWeylGroup i` (quotient of `normalizerPoints i` by `centralizerPoints i`) |
| `W_M` for `M = L_I` | `standardRelativeWeylGroup i ν (rootSet i ν I)`, the image of `L_I(k) ∩ N(k)` |
| `P_I = L_I U_I` | `parabolic i ν I`, `levi i ν I`, `unipotent i ν I` (rational points, `RationalPointFamily`) |
| `P_∅` | `parabolic i ν ∅` |
| `w·H` | `H.map (MulAut.conj n)` for a representative `n : normalizerPoints i` of `w` |
| length | `cs.length` for a Coxeter system `cs` satisfying `IsRelativeWeylCoxeterRealization i ν cs` |

`Q = LU` has index set `IL` and `P = MN` has index set `IM`. Inside the statement,
`Wmin IL IM` is the set (V.4.6.1): elements `w` with a representative `n` such that
`n (L ∩ P_∅) n⁻¹ ≤ P_∅` and `n⁻¹ (M ∩ P_∅) n ≤ P_∅`. `WLM IL IM` is `W(L, M)`:
elements with a representative `n` such that `n L n⁻¹ = M`. Both conditions do not
depend on the representative, because two representatives differ by `Z(k) ⊆ L ∩ M`,
which normalizes `L ∩ P_∅` and `M ∩ P_∅`.

For all index sets `IL` and `IM` the statement asserts:

- **(i)** every double coset `W_M w W_L` contains exactly one element of
  `Wmin IL IM`. For every Coxeter system `cs` on `relativeWeylGroup i` that
  realizes the root action, every `v ∈ Wmin IL IM` is strictly shorter than every
  other element `a v b` (`a ∈ W_M`, `b ∈ W_L`) of its double coset.
- **(ii)** for every representative `n` of an element of `Wmin IL IM`:
  - some `K ⊆ IM` satisfies `M ∩ nQn⁻¹ = M ∩ P_K`, `M ∩ nLn⁻¹ = L_K` and
    `M ∩ nUn⁻¹ = M ∩ U_K`;
  - some `K' ⊆ IL` satisfies `L ∩ n⁻¹Pn = L ∩ P_{K'}`, `L ∩ n⁻¹Mn = L_{K'}` and
    `L ∩ n⁻¹Nn = L ∩ U_{K'}`;
  - the four product decompositions hold as equalities of subsets of `G(k)`:
    `P ∩ nQn⁻¹ = (P ∩ nLn⁻¹)(P ∩ nUn⁻¹)`, `Q ∩ n⁻¹Pn = (Q ∩ n⁻¹Mn)(Q ∩ n⁻¹Nn)`,
    `N ∩ nQn⁻¹ = (N ∩ nLn⁻¹)(N ∩ nUn⁻¹)` and `U ∩ n⁻¹Pn = (U ∩ n⁻¹Mn)(U ∩ n⁻¹Nn)`.
- **(iii)** for every `w ∈ W(L, M)`, exactly one element of `Wmin IL IM ∩ WLM IL IM`
  lies in `w W_L`, and `W_M w ⊆ w W_L`.

## Formalization choices

- **Standard parabolic subgroups of `M` and `L`.** For `M = L_{IM}`, the standard
  parabolic subgroups of `M` (relative to `M ∩ P_∅`) are the `M ∩ P_K` with
  `K ⊆ IM`, with Levi factor `L_K` and unipotent radical `M ∩ U_K` (V.4.2 inside
  `M`). The statement therefore encodes "standard parabolic subgroup of `M` with
  Levi factor `M ∩ w·L` and unipotent radical `M ∩ w·U`" by the existence of `K`
  with the three displayed equalities, and likewise for `L`. Renard writes the
  `L`-side intersections as `w⁻¹·P ∩ L`. The statement writes `L ∩ n⁻¹Pn`, which
  is the same subgroup.
- **Length.** The framework has no canonical length function on
  `relativeWeylGroup i`. The published `IsRelativeWeylCoxeterRealization` gives
  the Coxeter systems whose simple reflections are the reflections of the simple
  relative roots, with length equal to the number of inverted reduced positive
  roots, as in Renard's proof. The minimality clause holds for every such system.
  Such a system exists: the published `RelativeWeylCoxeterStatement` asserts
  `HasRelativeWeylCoxeterSystem i ν`, and `relativeWeylCoxeter` proves it. So the
  minimality clause is not vacuous. The uniqueness clause of (i) uses no length.
- **(iii) as bijections.** The first clause of (iii) says that
  `Wmin ∩ W(L, M) → W(L, M)/W_L`, `v ↦ v W_L`, is a bijection (`W(L, M) W_L =
  W(L, M)`). The second clause says `W_M w W_L = w W_L` for `w ∈ W(L, M)`, so
  `W_M \ W(L, M)/W_L = W(L, M)/W_L`.
- **Inline sets.** `Wmin` and `WLM` are `let`-bound sets inside the statement. The
  Library has no named `W(L, M)` or `W^{L,M}` on the actual relative Weyl group.

## Related Library content

`Langlands.Group.RelativeWeylIndexing` and its proved companions
(`RelativeWeylMinimalUniqueProof`, `RelativeWeylMinimalityProof`) prove the
abstract Coxeter facts for an arbitrary Coxeter system: existence and uniqueness
of the minimal element of a parabolic double coset. This statement is the
group-level version. It defines `W^{L,M}` by containment in `P_∅`, it uses the
actual Weyl subgroups `W_M` of the standard Levis, and part (ii) is about subgroups
of `G(k)`. `RationalRootSignTarget` records V.4.6 as the source of the root-sign
comparison it formulates.

## Why the statement is true

Renard proves (ii) first. In terms of root subsets (V.4.2), `w ∈ W^{L,M}` means
`w·L⁺ ⊆ Σ⁺` and `w⁻¹·M⁺ ⊆ Σ⁺`. Then `M ∩ w·Q` is a parabolic subset of `M`, and
V.4.2 applied in `M` gives the parabolic triple. The decompositions follow from
the intersection formulas for closed root subsets (V.4.2, citing Borel–Tits 3.22).
For (i), length is the number of inverted positive roots, and `l(w s_γ) > l(w)`
exactly when `w·γ > 0`. So `W^{L,M}` is the set of `w` minimal for right
multiplication by `W_L` and left multiplication by `W_M` (V.4.6.2). Renard then
cites Bourbaki, *Groupes et algèbres de Lie*, Chap. IV, §1, exercise 3, and
Carter, *Finite groups of Lie type*, Prop. 2.7.3 (his [9] and [19]); the length
facts are from Steinberg's *Lectures on Chevalley groups* (his [43]). (iii) follows
from (i) and `W_M · W(L, M) · W_L = W(L, M)` (V.4.3).

## Remaining obligations

The proof is a separate obligation. It needs V.4.2 on the actual groups (the
published standard parabolic interface), the proved Coxeter realization
`relativeWeylCoxeter`, and the abstract double-coset results of
`Langlands.Group.RelativeWeylIndexing`.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement` | `IsRelativeWeylCoxeterRealization`, `relativeWeylGroup`, `standardRelativeWeylGroup` (through its imports) |
| `Langlands.Representation.Aubert.General.RationalPointFamily` | `SimpleRoot`, `rootSet`, `parabolic`, `levi`, `unipotent` |
