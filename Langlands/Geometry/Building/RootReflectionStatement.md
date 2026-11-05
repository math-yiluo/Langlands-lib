# The elements `m(u)` act on the apartment as affine reflections

Module `Langlands.Geometry.Building.RootReflectionStatement`.
The Prop-valued target `Langlands.Geometry.Building.RootReflectionStatement`
states Kaletha–Prasad Proposition 6.2.1 for the fixed apartment of building
data, in the form of AS 1 with the actual elements `m(u)`. No proof is
supplied. The statement asserts no existence of data.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), source ID
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Printed page numbers are PDF page numbers minus 31.

- §6.2 opening, printed p. 212 / PDF p. 243. `A` is an arbitrary
  equipollence class of valuations of the root datum of `(G, S)`, for a
  connected reductive `G` and a maximal split torus `S`. For
  `u ∈ U_a(k)^* = U_a(k) ∖ {1}` the hyperplane is
  `H_u = {φ ∈ A | φ_a(u) = 0}`.
- Proposition 6.2.1, printed pp. 212–214 / PDF pp. 243–245: "For
  `u ∈ U_a(k)^*`, let `m(u) = u′uu″` be as in Proposition 2.11.17. Then for
  `φ ∈ A`, `φ − m(u)φ = φ_a(u)a^∨`. Thus the action of `m(u)` on the set of
  valuations of the root datum of `(G, S)` preserves `A` and acts on it as the
  affine reflection in `H_u`." The general-case proof uses the valuation
  axioms V 2–V 5 and, for roots `b` that are not rational multiples of `a`,
  the bijection of an ordered product of filtration subgroups onto a
  commutative quotient `U/V`.

The corrections of 1 November 2024, source ID
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, have no
change to Proposition 6.2.1 in their Chapter 6 list (PDF p. 32). Their
addition to the opening of Chapter 7 (PDF p. 33) states that AS 1–AS 4 of
Axiom 4.1.6 are proved for these apartments.

## The Lean statement

```
∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffineHom G.X.hom] (B : ValuationBuildingData G),
  B.HasRootReflections
```

`B.HasRootReflections` is the published predicate of module
`ParahoricBuildingAxioms`. It says: for every relative root `α`, every
`u ∈ B.rootGroup α` with `u ≠ 1`, every pair `p` with
`RelativeRoot.IsOppositeFactorPair B.i α u p` (so `p.1, p.2 ∈ U_{-α}(F)` and
`m(u) = p.1 * u * p.2 ∈ N(F)`), and every point `x` of the apartment with
`x.val α u = 0`, the element `B.reflectionElement p` fixes `x`.

- `B : ValuationBuildingData G` consists of a connected reductive `G`, a
  maximal split torus `B.i : S → G`, an `N(F)`-stable equipollence class of
  valuations of the root datum compatible with `ord_F` on `S(F)`, the
  centralizer `Z_G(S)`, and V 6 on `Z(F)`. This is a special case of KP's
  setting, which needs neither V 6 nor a local field.
- The action of `N(F)` on the apartment is the published one,
  `(nφ)_a(g) = φ_{n⁻¹a}(n⁻¹ g n)` (KP 6.1.8). The fixed-point condition is
  therefore an equality of valuations, which is what KP's formula gives
  for `φ_a(u) = 0`.
- The predicate quantifies over every opposite factor pair. By KP
  Proposition 2.11.17 (`RootRankOneFactorizationStatement`, unproved in the
  Library) the pair is unique, so this is KP's `m(u)`.
- No apartment axiom (`SatisfiesApartmentAxioms`) is assumed. KP's
  proposition needs only the valuation axioms of the class.

Only the fixed-point form is stated. The linear part of the action of `n`
is `translationAction B.i n`. By KP Proposition 2.11.17 it is the reflection
`r_a` for `n = m(u)`, and then the fixed-point form is equivalent to KP's
formula `φ − m(u)φ = φ_a(u)a^∨`.

## Use

The sharp chamber factorization (`ValuationBuildingData.ChamberSharpDecompositionStatement`,
KP 7.3.12) needs the rank-one step of KP Proposition 7.1.1(1), printed
p. 237 / PDF p. 268. Its hypotheses are `u ∈ U_a(F)^*`, `u′ ∈ U_{-a}(F)^*`
and `φ_a(u) + φ_{-a}(u′) > 0`; without the last condition the
factorization fails: in `SL₂(ℚ₃)`, `u = [[1, 1], [0, 1]]` and
`u′ = [[1, 0], [-1, 1]]` have depths summing to `0` for the standard
valuation, and `uu′ = [[0, 1], [-1, 1]]` has upper-left entry `0`, which no
element of `U_{-a} Z U_a` has. Under these hypotheses the proof
of KP gives `uu′ = x′ z x` with `x ∈ U_a(F)^*`, `x′ ∈ U_{-a}(F)^*`,
`z ∈ Z(F)`, `φ_a(x) = φ_a(u)` and `φ_{-a}(x′) = φ_{-a}(u′)`, and the
identity `m(u′) = m(x′) z`. The present statement supplies the next step:
since `φ_{-a}(x′) = φ_{-a}(u′)`, the hyperplanes `H_{x′}` and `H_{u′}`
coincide, so `m(x′)` and `m(u′)` both fix every point of this hyperplane,
and hence so does `z = m(x′)⁻¹ m(u′)`. As `z ∈ Z(F)` acts on the apartment
by a translation, `z` fixes every point. This statement does not assert
the factorization or the depth equalities; they are proved separately.
