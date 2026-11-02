# Valuations of the root datum on the actual relative root groups

This module belongs to the task on actual Kaletha–Prasad affine-root,
special-point, parahoric and compact-stabilizer objects. It states the
Bruhat–Tits notion of a valuation of the root datum of `(G, S)` on the actual
relative root groups of the Library, and the two actions on such valuations.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`:

- Definition 6.1.2 (axioms V 0–V 7), printed p. 199, PDF p. 230;
- Remark 6.1.5, Lemma 6.1.6, Definition 6.1.7 and §6.1.8, printed
  pp. 200–201, PDF pp. 231–232;
- Proposition 2.11.17 (the elements `u′, u″` used in V 5), printed p. 136,
  PDF p. 167.

The registered corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`), Chapter 6 at PDF p. 32, do not change
Definition 6.1.2, Lemma 6.1.6, Definition 6.1.7 or §6.1.8. Their correction
to the proof of Lemma 6.1.12 writes out `n(φ + v) = nφ + w v`, which is the
law `smul_vadd` below.

## Setting

`k` is a field, `S` a commutative group scheme over `Spec k` and
`i : S.toGrp ⟶ G` a homomorphism into a group scheme `G`. The intended case is
KP's: `G` connected reductive and `i` the inclusion of a maximal `k`-split
torus. No reductivity, splitness or maximality hypothesis is imposed; the
definitions make sense for every such `i`. `V S` is the Library's real vector
space `V(S)` of `S` (from `RealTorusSpace`), `eval S a : V S →ₗ[ℝ] ℝ` is
evaluation `v ↦ a(v)` of a character `a`, and `relativeRoots i` is the
Library's set `Φ = Φ(S, G)`, which needs `[IsAffineHom G.X.hom]`.

- `rootGroupPoints i a : Subgroup (rationalPoints G)` is `U_a(k)`: the
  `k`-points of the published actual root subgroup functor
  `RelativeRoot.subgroup i a`. `mem_rootGroupPoints` unfolds it to the
  orbit-extension description of that functor. For a multipliable root `a` the
  same functor at `2 • a` is the actual `U_{2a}`. No representability or
  equivalence with KP's dynamic construction is asserted here (the Library's
  `RootSubgroup` module records that comparison as a separate obligation).
- `eval_zero_char`, `eval_add_char`, `eval_neg_char`, `eval_nsmul_char`:
  `a ↦ a(v)` is additive in the character.

## Families of functions and the two actions

KP's valuation is a family `(φ_a : U_a(k) → ℝ ∪ {∞})_{a ∈ Φ}`. Lean has no
convenient dependent family over a varying subgroup and a varying index set,
so `RootFunctionFamily S G` is a structure with one field
`toFun : characterLattice S → rationalPoints G → WithTop ℝ`, used as a function
through `CoeFun`, with `coe_mk` and `ext`. The axioms of a valuation (below)
require the value `∞` at every character that is not a root, and at every point
outside `U_a(k)`. So a family satisfying them is the same data as KP's family:
restrict to `a ∈ Φ` and `U_a(k)`, or conversely extend by `∞`. This
normalization is our formulation, not KP's. It does not change any
`U_{a,φ,r}`.

- Translation (KP before Lemma 6.1.6): `v +ᵥ φ` is
  `(v +ᵥ φ) a g = φ a g + a(v)` (`vadd_apply`). It is an `AddAction` of the
  additive group `V S`. KP write `φ_v = φ + v`.
- The normalizer (KP 6.1.8): for `n ∈ normalizerPoints i` (KP's `N(k)`),
  `(n • φ) a g = φ (n⁻¹·a) (n⁻¹ g n)` (`smul_apply`). This is KP's
  `n·φ_a(u) = φ_{n⁻¹·a}(n⁻¹ u n)`. Here `n·a` is the published
  `weylAction i n a`, with `(n·a)(s) = a(n⁻¹ s n)`. It is a `MulAction`, which
  needs `[Mono i.hom.hom.left]` as `weylAction` does.
- `smul_vadd`: `n • (v +ᵥ φ) = (n • v) +ᵥ (n • φ)`. This is KP's
  `n·(φ + v) = n·φ + n·v` from the identity `a(n·v) = (n⁻¹·a)(v)`, which is
  the published `eval_normalizer_smul`. Both actions are defined on all
  families, not only on valuations. KP's claim that `nφ` is again a valuation
  is not proved here (see the last section).

## Filtration sets and equipollence

- `rootFiltration i φ a r` is `U_{a,φ,r} = φ_a⁻¹([r, ∞]) ⊆ U_a(k)` for real
  `r`, as a set (`mem_rootFiltration`). KP Remark 6.1.5 notes that `u` lies in
  it iff `r ≤ φ_a(u)`; that is the definition used here. Axiom V 1 says that it
  is a subgroup.
- `rootFiltration_vadd`: `U_{a,φ+v,r+a(v)} = U_{a,φ,r}`, the second statement
  of KP Lemma 6.1.6. `rootFiltration_vadd'` is the same with `r` shifted.
- `Equipollent φ ψ` is `∃ v, ψ = v +ᵥ φ` (KP Definition 6.1.7, written with
  KP's `φ′_a(u) = φ_a(u) + a(v)`). `equipollent_iff_mem_orbit` identifies it
  with the `V(S)`-orbit. `Equipollent.refl`, `.symm` and `.trans` make it an
  equivalence relation, as KP note.

## The axioms (`IsRootDatumValuation`)

`IsRootDatumValuation i φ` is a structure of propositions. Its fields are
listed with KP's axioms below. `a, b` range over `relativeRoots i` throughout.

- `eq_top_of_not_mem_roots`, `eq_top_of_not_mem`: the normalization to `∞`
  explained above.
- `three_le_encard` (V 0): `φ_a(U_a(k))` has at least 3 elements, counted
  with `Set.encard`.
- `one_mem`, `mul_mem`, `inv_mem` (V 1): for every real `r`,
  `U_{a,φ,r}` contains `1` and is closed under products and inverses. It is
  then a subgroup of `U_a(k)`, since it is contained in `U_a(k)` by
  definition.
- `eq_top_iff` (V 1): for `g ∈ U_a(k)`, `φ_a(g) = ∞ ↔ g = 1`, that is,
  `U_{a,φ,∞} = φ_a⁻¹(∞) = {1}`.
- `reflection` (V 2): for every `n ∈ N(k)` realizing the reflection along `a`,
  there is a real `c` with `φ_a(u) = φ_{-a}(n u n⁻¹) + c` for all
  `u ∈ U_a(k) ∖ {1}`. KP say that `u ↦ φ_a(u) − φ_{-a}(n u n⁻¹)` is constant on
  `U_a(k)∗`. We write it additively because `WithTop ℝ` has no subtraction
  with good laws. Both values are finite there: `u ≠ 1` gives `φ_a(u) ≠ ∞` by
  V 1, and the equation then forces `φ_{-a}(n u n⁻¹) ≠ ∞`. So the two forms
  agree.
- `commutator` (V 3): if `b ∉ −ℝ_{>0}·a`, then for all real `r, s`,
  `⁅U_{a,φ,r}, U_{b,φ,s}⁆` lies in the subgroup generated by the
  `U_{pa+qb,φ,pr+qs}` with integers `p, q > 0` and `pa + qb ∈ Φ`. The
  condition `b ∉ −ℝ_{>0}·a` is stated in `Vstar S = ℝ ⊗ X*(S)`, as
  `1 ⊗ b ≠ −t (1 ⊗ a)` for all real `t > 0`. The commutator is Mathlib's
  commutator of subgroups, the subgroup generated by all commutators, which is
  KP's commutator subgroup `(H, K)`. It is applied to the subgroups generated by
  the filtration sets; by V 1 these are the filtration sets themselves.
  KP write `i, j` for the reals and `Z_{>0}` for the integers; we use `r, s`
  and natural numbers `p, q` with `0 < p`, `0 < q`.
- `double` (V 4): if `a, 2a ∈ Φ`, then `φ_{2a}(u) = 2 φ_a(u)` for every
  `u ∈ U_{2a}(k)`. KP's restriction `φ_a|U_{2a}(k)` uses
  `U_{2a}(k) ⊆ U_a(k)`. That inclusion is not proved in the Library. The field
  is stated for all `u ∈ U_{2a}(k)` as written. KP's consequence
  `U_{a,φ,r} ∩ U_{2a}(k) = U_{2a,φ,2r}` is not stated.
- `opposite` (V 5): for `u ∈ U_a(k) ∖ {1}` and `u′, u″ ∈ U_{-a}(k)` with
  `u′ u u″ ∈ N(k)`, `φ_{-a}(u′) + φ_a(u) = 0`. KP take `u′, u″` as in
  Proposition 2.11.17, which says such a pair exists and is unique. So
  quantifying over all such pairs is the same condition. That proposition
  needs `u ≠ 1`, so KP's `u ∈ U_a(k)` means `u ∈ U_a(k)∗`, as used here. Since
  `φ_a(u)` is finite, the sum form is KP's `φ_{-a}(u′) = −φ_a(u)`.

"`n` realizes the reflection along `a`" is `RealizesReflection i a n`:
`n·a = −a`, and `n` fixes the hyperplane `ker a ⊆ V(S)` pointwise. KP mean
that the image of `n` in `W = N(k)/Z(k)` is the reflection `r_a`. This
characterization is our own formulation, explained as follows. `W` acts
faithfully on `V(S)` (KP 6.1.8: the kernel of the action of `N(k)` on `X*(S)`
is `Z(k)`). An element of `GL(V(S))` that fixes `ker a` pointwise and sends
`a` to `−a` has the form `v ↦ v − a(v) w` with `a(w) = 2`. Two such elements of
the finite group `W` differ by a transvection of finite order, so they are
equal. Since `r_a ∈ W`, the elements satisfying the condition are exactly the
`n` with image `r_a`. This argument uses facts about `W` that are not in the
Library and is not formalized. The Lean condition is stated directly, without
reference to `W`.

## The split-torus part of V 6

`IsSplitTorusCompatible i ω φ` is stated for a function `ω : kˣ → ℝ`, meant
to be the valuation of `k`. It is the condition
`φ_a(s⁻¹ u s) = φ_a(u) − ω(a(s))` for `a ∈ Φ`, `s ∈ S(k)` and `u ∈ U_a(k)`,
with `s` mapped into `G(k)` by `i` and `a(s)` the published
`rationalCharacterEval`. KP state this as the "in particular" case of V 6 for
`s ∈ S(k)`. Full V 6 is the same formula for all `z ∈ Z(k)` with `a(ν(z))`,
where `ν : Z(k) → V(S′)` is the homomorphism of KP Axiom 4.1.4(A 1). The
Library has no `ν`, so only this part is stated. It is a separate predicate
because KP define ω-compatibility separately from Definition 6.1.2.

Proved laws:

- `IsRootDatumValuation.vadd`: if `φ` is a valuation then so is `v +ᵥ φ` for
  every `v ∈ V(S)` (KP Lemma 6.1.6, first statement), for every field. The
  proof shifts each value by `a(v)`: V 0 by injectivity of `x ↦ x + a(v)`; V 1
  and V 3 by `rootFiltration_vadd'` and additivity of `a ↦ a(v)` (with
  `(pa+qb)(v) = p a(v) + q b(v)`); V 2 with the new constant `c + 2a(v)`; V 4
  from `(2a)(v) = 2a(v)`; V 5 since `(−a)(v) + a(v) = 0`.
- `IsSplitTorusCompatible.vadd`: a translate of an ω-compatible family is
  ω-compatible (KP after Definition 6.1.7). The proof is a commutation of
  additions.

## Not formalized

- V 7 (compatibility with the topology) and full V 6 on `Z(k)`.
- That `n • φ` is a valuation when `φ` is (KP 6.1.8, "easily seen"). This
  needs `n U_a(k) n⁻¹ = U_{n·a}(k)`, `n·Φ = Φ` and the corresponding facts
  for `N(k)`-conjugates of the elements of Proposition 2.11.17. These are not
  in the Library.
- The action of `N_ad(k)` (KP 6.1.8, second paragraph).
- Existence of a valuation for any `G`, and the remaining statements of KP
  Remarks 6.1.4–6.1.5 (for example `φ_a(u⁻¹) = φ_a(u)`).
