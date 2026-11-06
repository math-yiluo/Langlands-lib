# Finite parabolic double cosets with torus-adapted representatives

`Langlands.GroupScheme.RepresentedParabolicDoubleCosetStatement` is a
proposition about two parabolic subgroups of a connected reductive group over
an arbitrary field `k`. It makes two claims.

1. The double-coset space `P(k) \ G(k) / Q(k)` is finite.
2. Every double coset `P(k) g Q(k)` has a representative `z` such that some
   maximal split torus of `G` lies in both `M` and `z L z⁻¹`.

## Hypotheses

- `G` is a connected reductive group scheme over `Spec k`
  (`IsConnectedReductive`).
- `p : P ⟶ G` and `q : Q ⟶ G` are parabolic subgroups
  (`IsParabolicSubgroup`): smooth closed subgroups whose base change to the
  algebraic closure contains a Borel subgroup. These are Borel–Tits's
  `k`-parabolic subgroups.
- `l : M ⟶ P` and `lQ : L ⟶ Q` are rational Levi subgroups
  (`IsRationalLeviSubgroup`). Each is a closed, connected reductive subgroup
  with a complementary geometric unipotent radical, so the product map is an
  isomorphism onto the parabolic.

No minimal parabolic, standardness or common torus is assumed.

## Conclusion in Lean

The double cosets are Mathlib's `DoubleCoset.Quotient` of the group
`rationalPoints G` by the literal point images `(rationalPoints.map p).range`
and `(rationalPoints.map q).range`, coerced to sets. The first conjunct says
this quotient is `Finite`.

The second conjunct says that for every `g : rationalPoints G` there is a
`z : rationalPoints G` with
`DoubleCoset.mk _ _ z = DoubleCoset.mk _ _ g` (the same double coset) and a
commutative group scheme `T` with `i : T.toGrp ⟶ G` such that

- `IsMaximalSplitTorus i` holds;
- `i` factors through `M`: `a ≫ l ≫ p = i` for some `a : T.toGrp ⟶ M`;
- `i` factors through `z L z⁻¹`: `b ≫ lQ ≫ q ≫ (G.innerIso z).hom = i` for
  some `b : T.toGrp ⟶ L`.

`G.innerIso z` is the inner automorphism of `G` determined by `z`. On rational
points it is `x ↦ z x z⁻¹` (`rationalPoints_map_innerIso`), so
`lQ ≫ q ≫ (G.innerIso z).hom` is the subgroup `z L z⁻¹`. Containment is
expressed by factorization of morphisms. The tori `T`, `i` and the factors
are existentially quantified; nothing is chosen globally.

## Sources

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, 2026 version (`renard-2026-representations-groupes-reductifs-padiques`),
and Armand Borel and Jacques Tits, *Groupes réductifs*, Publ. Math. IHÉS 27
(1965) (`borel-tits-1965-groupes-reductifs`).

- Finiteness is Renard V.4.5, Corollaire (printed p.120 / PDF p.126): for two
  parabolic subgroups `P = MN` and `Q = LU` of `G`, the set of `Q`-orbits in
  `P \ G` is finite. Renard deduces it from the lemma before it (printed
  p.119 / PDF p.125), which identifies the orbits with `W_M \ W_G / W_L` for
  semi-standard parabolics with standard Levis, and from the conjugacy of every
  parabolic to a standard one. Over an arbitrary field the corresponding
  results are Borel–Tits 5.20 (printed p.102 / PDF p.49), the bijection between
  `P_Θ(k) \ G(k) / P_Θ'(k)` and `W_Θ \ W / W_Θ'`, and 4.13 b) (printed p.90 /
  PDF p.37), conjugacy of minimal `k`-parabolics.
- The representatives are Renard V.4.7 (printed pp.121–122 / PDF pp.127–128).
  With `P₁ = g·P`, `Q₁ = h·Q` standard, `M₁ = g·M`, `L₁ = h·L` standard Levis,
  Renard takes `z = g⁻¹ w h` with `w` a representative of an element of
  `W_{L₁,M₁}` in `N_G(A_∅)`, and shows these exhaust `P \ G / Q`.

## Provenance of the torus clause

The torus clause is derived; Renard does not state it. For Renard's
representative `z = g⁻¹ w h`, the standard Levi subgroups `M₁` and `L₁` both
contain the fixed maximal split torus `A_∅`, and `w` normalizes `A_∅`. Hence
`M = g⁻¹ M₁ g` contains `g⁻¹ A_∅ g`, and
`z L z⁻¹ = g⁻¹ w L₁ w⁻¹ g` contains `g⁻¹ w A_∅ w⁻¹ g = g⁻¹ A_∅ g`.

The clause also follows from Borel–Tits directly, for a representative in any
double coset. By Borel–Tits 4.18 (printed p.92 / PDF p.39), `P ∩ g Q g⁻¹`
contains the centralizer of a maximal split torus `S`. By 4.15–4.16 and the
`k`-conjugacy of `k`-Levi subgroups under `R_u(P)(k)` (3.14, used in the same
way in the proof of 5.15, printed p.100 / PDF p.47), there are `u ∈ P(k)` and
`v ∈ Q(k)` with `S ⊂ u M u⁻¹` and `S ⊂ (g v) L (g v)⁻¹`. Then
`z = u⁻¹ g v` lies in `P(k) g Q(k)`, and `u⁻¹ S u` is a maximal split torus
in `M ∩ z L z⁻¹`.

This is the form in which the published
`RepresentedGeometricLemmaGeometryStatement` uses the representatives: its
intersection datum includes a maximal split torus of `G` in `M ∩ z L z⁻¹`.

## Scope

Renard works over a nonarchimedean local field. This statement is algebraic
and is stated over every field `k` with no topology; Borel–Tits's results hold
in that generality. It asserts nothing about the intersection subgroups
themselves. Their structure is the separate statement
`RepresentedParabolicLeviIntersectionStatement`.
