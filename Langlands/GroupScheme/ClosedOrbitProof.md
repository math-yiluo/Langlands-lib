# Proof that smooth affine group actions have a closed orbit

Proof author: Worker 716. Worker 135 checked the current-Library build, the exact
statement and original source, and prepared this submission and its explanation.
The statement `ClosedOrbitStatement` was written by Worker 1396.

The module proves

```
theorem Langlands.GroupScheme.closedOrbit : ClosedOrbitStatement.{u}
```

for the proposition of `Langlands.GroupScheme.ClosedOrbitStatement`, at arbitrary
universe `u`. Fix an algebraically closed field `k` and write `S = Spec k`. Let
`G` be a group scheme over `S` with `G.X.hom` smooth and affine, and let `X : Over S`
be locally of finite type and quasi-compact, with `X.left` nonempty. Let
`a : SchemeAction G X` be an action. The proof builds a reduced closed subscheme
`j : O ⟶ X`, an action `b` of `G` on `O` compatible with `a`, and a rational point
`x` of `O` whose orbit contains every rational point of `O`.

The proof follows the orbit lemma of Milne, *Algebraic Groups* (2017), Proposition
1.65 and Proposition 1.66 with the remark after its proof (printed pp.26–28). The
orbit map has constructible image (Chevalley's theorem), so the image contains a
dense open subset of its closure. Milne takes an orbit of minimum dimension. The
Lean proof instead takes a minimal nonempty closed subset stable under the rational
points of `G` and shows that this subset is a single orbit. Noetherian induction
on closed sets gives this minimal subset, so no dimension theory is needed.

The source is registered as `milne-2017-algebraic-groups`; the locator is
Propositions 1.65(b)–(c) and 1.66 and its following remark, printed pp.26–28
(one-based PDF pp.42–44). The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` corrects the order of choosing a
flat open set and extending the field in the proof of 1.65(a). This module does
not use that generic-flatness argument. It constructs the restricted scheme
action directly, using reducedness and closed-point density, and proves orbit
surjectivity and rational transitivity as described below.

## Constructible sets (namespace `Langlands.GroupScheme.ClosedOrbit`)

- `constructible_dichotomy`: let `s` be a constructible subset of a topological
  space and `W` an irreducible subset. Then some open `U` meets `W` with
  `U ∩ W ⊆ s`, or some open `U` meets `W` with `U ∩ W ⊆ sᶜ`. The proof is by
  Mathlib's induction principle `IsConstructible.empty_union_induction`
  (retrocompact opens, finite unions, complements). For an open set `U`, take `U`
  itself if it meets `W`, and otherwise take the whole space, which meets `W` inside
  `Uᶜ`. For a union `s ∪ t` where neither part gives the first alternative, the two
  opens `U₁` and `U₂` from the second alternatives both meet `W`. By irreducibility
  `U₁ ∩ U₂` meets `W`, and `U₁ ∩ U₂ ∩ W` misses `s ∪ t`. Complements exchange the
  two alternatives.
- `exists_isOpen_subset_of_dense`: in a nonempty noetherian space, a dense
  constructible set contains a nonempty open set. Mathlib's
  `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` gives a
  nonempty open `o` inside an irreducible component, so `o` is irreducible. Apply
  `constructible_dichotomy` to `o`. In the first case `U ∩ o` is the open set. The
  second case is impossible, because the nonempty open `U ∩ o` misses the dense set.

## Translations by rational points

For a point `g : 𝟙_ ⟶ G.X` over the base and an action `a` of `G` on `O`, the
proof reuses two Library maps and their lemmas:

- `FiniteIndexTransfer.leftMul G g : G.X ⟶ G.X`, left multiplication by `g`
  (module `Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof`);
- `OrbitMapFlat.actBy a g = a.act (toUnit O ≫ g) (𝟙 O) : O ⟶ O`, the action of `g`
  (module `Langlands.GroupScheme.OrbitMapFlatProof`).

From the same Library module, `actBy_comp_actBy` gives
`actBy a g ≫ actBy a h = actBy a (h * g)` and `actBy_one` gives `actBy a 1 = 𝟙 O`.
`leftMul_comp_orbit` states that `leftMul G g ≫ π = π ≫ actBy a g` for the orbit map
`π = a.act (𝟙 G.X) (toUnit G.X ≫ x)`. `comp_actBy` and `comp_orbit` evaluate
`actBy a g` and `π` on rational points.

This module adds two lemmas in namespace `Langlands.GroupScheme.ClosedOrbit`.
`comp_actBy_of` evaluates `actBy a g` on points over an arbitrary `T`:
`y ≫ actBy a g = a.act (toUnit T ≫ g) y`. It follows from the Library's
`SchemeAction.naturality`. `act_apply` states that `a.act g y`, evaluated at the
closed point of `Spec k`, equals `actBy a g` applied to the image of `y`. It
follows from the Library's `comp_actBy`.

## The main proof

1. **Minimal stable closed set.** `X.left` is locally noetherian (local finite type
   over a field) and compact (`QuasiCompact X.hom`), so it is a noetherian space.
   Its closed sets therefore satisfy `WellFoundedLT`. Call a set stable if
   `actBy a g` maps it into itself for every rational `g`. Among nonempty stable
   closed sets (the whole space is one, since `X.left` is nonempty), choose a
   minimal `Z`.
2. **The reduced subscheme.** Let `O` be the closed subscheme of the vanishing
   ideal of `Z`, with `j` its closed immersion. `O.left` is reduced by the
   Library's `Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker`,
   and the range of `j` is `Z` by Mathlib's `range_subschemeι`. `O.hom` is the
   closed immersion followed by `X.hom`, so it is locally of finite type and
   quasi-compact. `O.left` is therefore noetherian and Jacobson
   (`LocallyOfFiniteType.jacobsonSpace`), and it is quasi-separated over the
   affine base.
3. **The action lands in `Z`.** `G.X.hom` is geometrically reduced by the
   Library's `geometricallyReduced_of_smooth`. So `G.X ⊗ O`, the fibre product over
   `Spec k`, is reduced by Mathlib's instance for such pullbacks. It is also locally
   of finite type, hence Jacobson. Let `m = (G.X ◁ j) ≫ a.hom`. The preimage of `Z`
   under `m` is closed and contains every closed point `w`. Such a `w` is the image
   of a rational point `p` of `G.X ⊗ O` (Mathlib's `pointOfClosedPoint`, which uses
   that `k` is algebraically closed), and `m(w)` is `g • j(o)` for the components
   `g, o` of `p` (`act_apply`). This lies in `Z` by stability. Closed points are
   dense (`closure_closedPoints`), so the range of `m` lies in `Z`, the range of `j`.
4. **The restricted action.** The source of `m` is reduced and `j` is a closed
   immersion. So the Library's `FiniteIndexTransfer.exists_lift_of_range_subset`
   factors `m` as `hom ≫ j`. Because `j` is a monomorphism, the identities
   `(lift f o ≫ hom) ≫ j = a.act f (o ≫ j)` turn the identity and multiplication
   laws of `a` into those of `hom` on every test scheme. The Library's
   `schemeActionOfPointLaws` then makes `hom` an action `b`. The same identity is
   the equivariance clause `b.act g o ≫ j = a.act g (o ≫ j)`.
5. **Minimality on `O`.** Let `C` be a nonempty closed subset of `O.left` that is
   stable under every `actBy b g`. Its image under the closed embedding `j` is
   closed, nonempty, contained in `Z`, and stable under `a`, because
   `actBy b g ≫ j = j ≫ actBy a g` (by `comp_actBy_of` and the equivariance
   identity of step 4). Minimality makes this image equal to `Z`, and
   injectivity of `j` gives `C = O.left`.
6. **A rational point and its orbit map.** `O.left` is nonempty and Jacobson, so it
   has a closed point, which gives a rational point `x`. Let `π` be its orbit map.
   `π.left ≫ O.hom = G.X.hom`. Here `G.X.hom` is locally of finite type (smooth)
   and quasi-compact (affine), so `π.left` is locally of finite type and
   quasi-compact. The range of `π` is stable (`leftMul_comp_orbit`). Its closure is
   then a nonempty stable closed set, so by step 5 the range of `π` is dense.
7. **An open part of the orbit.** `π.left` is locally of finite presentation,
   because its target is locally noetherian. It is also quasi-compact, and `O.left`
   is quasi-compact and quasi-separated. Mathlib's `Scheme.Hom.isConstructible_image`
   (Chevalley's theorem) therefore makes the range of `π` constructible.
   `exists_isOpen_subset_of_dense` then gives a nonempty open `N` inside the range.
8. **Surjectivity.** Suppose some `w` had no rational `g` with `g • w ∈ N`. Then
   `C = ⋂_g (actBy b g)⁻¹(Nᶜ)` is closed, contains `w`, and is stable by
   `actBy_comp_actBy`. By step 5, `C` is everything, and with `g = 1` this makes `N`
   empty, a contradiction. So each `w` has some `g` with `g • w ∈ N ⊆ range π`.
   Stability of the range under `g⁻¹` gives `w ∈ range π`.
9. **Rational transitivity.** Let `y` be a rational point of `O`. Its image point
   is closed (Mathlib's `pointEquivClosedPoint`). Its fibre under `π` is then a
   nonempty closed subset of the Jacobson space `G.X.left`, so it contains a closed
   point `z`. That point gives a rational point `g` of `G`. By `comp_orbit`,
   `b.act g x = g ≫ π`. This rational point agrees with `y` at the closed point of
   `Spec k`, so the two are equal by Mathlib's `ext_of_apply_closedPoint_eq`.

The remaining conclusions hold by construction: `O.left` is reduced, `j.left` is a
closed immersion, and `O.hom` is locally of finite type and quasi-compact.

## Use of the hypotheses

- `IsAlgClosed k`: closed points of schemes locally of finite type over `k` are
  rational points (steps 3, 6 and 9).
- `Smooth G.X.hom`: geometric reducedness, which makes `G.X ⊗ O` reduced (step 4).
  It also gives local finite type of `G.X.hom`, used for the Jacobson property of
  `G.X ⊗ O` and `G.X.left` and for `π` (steps 3, 6, 9).
- `IsAffineHom G.X.hom`: quasi-compactness of `G.X.hom`, hence of `π` (steps 6
  and 7).
- `LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`: `X.left` is noetherian
  (step 1), and `O` inherits finiteness (step 2).
- `Nonempty X.left`: the minimal set `Z` exists and is nonempty (steps 1 and 6).

Separatedness of `X` is not used.

## Scope of this contribution

This is an intermediate closed-orbit result for the Borel-conjugacy program.
It proves exactly `ClosedOrbitStatement.{u}`, with no additional hypothesis on
`X` or `G`. In particular, it assumes neither separatedness, reducedness nor
irreducibility of `X`, and neither connectedness nor reductivity of `G`.
It does not prove `BorelConjugacyStatement`, construct a Borel subgroup or its
proper quotient, or prove the solvable fixed-point theorem. Those are separate
consumer obligations.
