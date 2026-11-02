# Statement: the Coxeter system of the actual relative Weyl group

This file states that the published relative Weyl group
`relativeWeylGroup i = N(k)/Z(k)` of a maximal split torus `i : T ⟶ G` of a
connected reductive group `G` over an arbitrary field `k` is a finite Coxeter
group. Its simple reflections are labelled by the published simple relative
roots of a generic cocharacter, and the Coxeter structure is tied to the actual
root action, to lengths and signs, and to the published standard relative Weyl
subgroups. The file contains definitions and the statement only. No proof of the
final statement is given.

## Published objects used

- `relativeWeylGroup i`: the quotient of `normalizerPoints i` by
  `centralizerPoints i`. These are the `k`-points of the normalizer and of the
  centralizer of the torus.
- `relativeRoots i`: the full set of relative roots, which may be nonreduced.
- `positiveRelativeRoots i ν`: relative roots `α` with `0 < ⟨α, ν⟩`.
- `simpleRelativeRoots i ν`: positive relative roots that are not the sum of two
  positive relative roots. They are computed in the full, possibly nonreduced,
  set of roots. If `2a` is a root, then `2a = a + a` is not simple, so this set is
  the base `Δ` of the reduced root system.
- `SimpleRoot i ν` (Aubert, `RationalPointFamily`): the subtype of
  `simpleRelativeRoots i ν`. `rootSet i ν I` is the set of characters underlying a
  finite set `I` of labels.
- `schemeWeylCharacterAction i : relativeWeylGroup i →* (X*(T) ≃ₗ[ℤ] X*(T))`
  (Aubert, `RationalWeylRootAction`): the action of `N(k)/Z(k)` on the full
  character lattice, descended from the published `weylAction i`.
- `standardRelativeWeylGroup i ν J`: the image in `relativeWeylGroup i` of the
  normalizer points that lie in the published standard Levi of `J`.
- `standardSubgroup cs I` (Aubert, `RelativeWeylIndexing`): the subgroup generated
  by the simple reflections `cs.simple a` for `a ∈ I`.
- `IsGenericCocharacter i ν`: `⟨α, ν⟩ ≠ 0` for every relative root `α`.

## New definitions

- `reducedPositiveRelativeRoots i ν`: the positive relative roots `α` such that no
  `n • β` with `n ≥ 2` and `β ∈ relativeRoots i` equals `α`. This is Renard's
  reduced set `Σ`: the roots `α` with `α/n ∉ Σ'` for `n ≥ 2`. The lemma
  `reducedPositiveRelativeRoots_subset_positive` records the inclusion.
- `relativeInversionSet i ν w`: the reduced positive roots `α` such that
  `-(w α)` is positive, that is, `w α ∈ -Σ⁺`.
- `IsRelativeWeylCoxeterRealization i ν cs` is defined for a Coxeter system `cs`
  of type `M : CoxeterMatrix (SimpleRoot i ν)` on `relativeWeylGroup i`. It is the
  conjunction of five conditions:
  1. **Integral reflection.** For each label `a` there is an additive map
     `f : X*(T) →+ ℤ` with `f a = 2` and
     `cs.simple a • χ = χ - f χ • a` for every character `χ`.
  2. **Positive roots.** `cs.simple a` sends every positive relative root other
     than `a` and `2 • a` to a positive relative root.
  3. **Sign and length.** For all `w` and `a`,
     `ℓ(w) < ℓ(w · cs.simple a)` if and only if `w a` is positive.
  4. **Length.** `ℓ(w)` is the cardinality `ncard` of `relativeInversionSet i ν w`.
  5. **Parabolic subgroups.** For every finite set of labels `I`,
     `standardSubgroup cs I = standardRelativeWeylGroup i ν (rootSet i ν I)`.
- `HasRelativeWeylCoxeterSystem i ν`: `relativeWeylGroup i` is finite,
  `SimpleRoot i ν` is finite, and there exist a Coxeter matrix `M` and a Coxeter
  system `cs` with `IsRelativeWeylCoxeterRealization i ν cs`.

Two small lemmas are proved. `rootSet_singleton` gives `rootSet i ν {a} = {a}`.
`IsRelativeWeylCoxeterRealization.simple_mem_standardRelativeWeylGroup` shows
that `cs.simple a` lies in `standardRelativeWeylGroup i ν {a}`; it follows from
condition 5 for `I = {a}`.

## The final statement

`RelativeWeylCoxeterStatement` quantifies over the universe-`u` field `k`, the
group scheme `G` with `IsConnectedReductive G`, the commutative group scheme `T`,
the homomorphism `i : T.toGrp ⟶ G` with `IsMaximalSplitTorus i`, and the
cocharacter `ν`. The hypotheses follow the published `Rational/Statement`. The
instances `IsAffineHom G.X.hom` and `Mono i.hom.hom.left` are obtained from the
reductive and maximal-split hypotheses. Under `IsGenericCocharacter i ν` the
statement concludes `HasRelativeWeylCoxeterSystem i ν`.

The only premises are the intrinsic hypotheses: connected reductive, maximal
split and generic. No Coxeter realization, reflection theorem or root-system
existence is assumed. Nonreduced root systems are retained, since `relativeRoots`
is the full set and condition 2 excludes both `a` and `2a`. Rank zero is retained
too: when there are no relative roots, `SimpleRoot i ν` is empty, and the
statement says that `relativeWeylGroup i` is trivial with the empty Coxeter system.

## Sources

Borel–Tits, *Groupes réductifs* (1965), source
`borel-tits-1965-groupes-reductifs`. Printed page = PDF page + 53.

- Théorème 5.3, printed p.96 (PDF p.43): "Le groupe `_kW(G)`, vu comme groupe
  d'automorphismes de `X*(S)⊗ℝ` muni d'un produit scalaire admissible, est
  engendré par les symétries par rapport aux hyperplans annulant une k-racine."
  Hence `N(k)/Z(k)` is the Weyl group of `_kΦ`. It is finite, and it is a Coxeter
  group on the reflections of the simple roots.
- Corollaire 5.8, printed p.98 (PDF p.45): for `a ∈ _kΦ` and `c ∈ X*(S)`,
  `2(a, c)/(a, a)` is an integer, and `r_a(c) = c − 2(a,c)(a,a)⁻¹ a`. This gives
  condition 1 with `f c = 2(a, c)/(a, a)`, on the whole character lattice and not
  only on the root span.
- 5.15–5.18, printed pp.100–101 (PDF pp.47–48): the `k`-points of a minimal
  standard `k`-parabolic subgroup and of `N(S)` satisfy the axioms of a Tits
  system ("5.15 et 5.16 montrent que les axiomes de [33] sont vérifiés"). Its Weyl
  group is `_kW`, with the fundamental reflections as generators. Proposition
  5.17: "Le groupe de Weyl relatif de `Z_θ` est `W_θ`", where `W_θ` is generated
  by the fundamental reflections of the simple roots in `θ`. This is condition 5.

Renard, *Représentations des groupes réductifs p-adiques* (French 2026 version),
source `renard-2026-representations-groupes-reductifs-padiques`. Printed page =
PDF page − 6.

- V.3.4, printed p.110 (PDF p.116): the reduced roots `Σ(A)` are the elements
  `α ∈ Σ'(A)` such that `α/n ∉ Σ'(A)` for `n ≥ 2`.
- V.3.7, printed p.111 (PDF p.117): `Σ(A)` is a root system ([BT] 5.8), and
  `W(A)` is identified with its Weyl group ([BT] 5.3).
- V.4.6, printed pp.120–121 (PDF pp.126–127). The length `l(w)` is the number of
  `γ ∈ Σ⁺` with `w·γ ∈ −Σ⁺` (condition 4). If `w ∈ W_L`, then
  `w·(Σ⁺ \ L⁺) ⊂ Σ⁺ \ L⁺` (condition 2, for `L = {a}`). Finally,
  `l(w s_γ) > l(w)` if and only if `w·γ ∈ Σ⁺` (condition 3).

The 2010 errata, `renard-2010-corrections-complements`, contain no correction to
these items.

## Derived formulations

Renard works over a non-archimedean local field. Borel–Tits works over an
arbitrary field, and the statement applies to every field `k` through Borel–Tits
5.3, 5.8 and 5.15–5.17. The root-system facts in conditions 2–4 are standard
properties of the Weyl group of the reduced system `Σ`, quoted from Renard.

- **Condition 2** uses the full positive set `Σ'⁺`. Renard's statement concerns
  reduced roots. If `β` is a positive root not proportional to `a`, then `β` is
  either reduced or twice a reduced root `γ` not proportional to `a`, and
  `s_a β = 2 s_a γ`. The only positive roots proportional to the simple root `a`
  are `a` and `2a`, because `a` is indivisible.
- **Condition 4** counts only reduced positive roots. This is Renard's count over
  `Σ⁺`.
- **Conditions 3 and 4** use the order defined by the generic cocharacter `ν`. Its
  positive system has base `simpleRelativeRoots i ν`.
- **Condition 5** compares two subgroups of the same group. On one side is the
  Coxeter parabolic subgroup, generated by the simple reflections. On the other
  is the published `standardRelativeWeylGroup`, defined by normalizer points in
  the published standard Levi, the intersection of the centralizers of the
  standard cocharacters of `J`. Borel–Tits 5.17 identifies them once that Levi is
  identified with `Z_θ`. Proving that identification is part of the proof of the
  statement, not a premise.

The Coxeter system is not unique, so it is asserted to exist. Conditions 1 and 5
fix `cs.simple a` as the reflection of `a` in `N(k)/Z(k)`.
