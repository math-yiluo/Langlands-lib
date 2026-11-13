# Zero-group fixers over the maximal unramified extension depend only on affine-root signs

`Langlands.Geometry.Building.UnramifiedZeroFixerAffineRootStatement` is an
unproved proposition, published as an interface. The module proves nothing
else. Its one private instance only records that the base change of an affine
group scheme is affine, by pullback-stability of affine morphisms.

## The statement

The proposition is universe polymorphic: `UnramifiedZeroFixerAffineRootStatement.{u}`.
At each universe `u` it ranges over:

- every `F : Type u` with `Field F`, `ValuativeRel F`, `TopologicalSpace F`
  and `IsNonarchimedeanLocalField F`, in equal and mixed characteristic;
- every group scheme `G` over `Spec F` with `IsAffineHom G.X.hom`, and no
  other hypothesis on `G`.

Write `K = inertiaFixedField F`, the maximal unramified extension of `F`
inside the chosen separable closure, and `G_K = baseChanged F K G`. The
statement then ranges over:

- every `C : MaximalUnramified.BuildingData F G_K`, the published supplied
  building data of `G_K` for the constructed normalized integer valuation of
  `K`. An element supplies connected reductivity of `G_K`, a maximal split
  torus `S`, a `KPApartmentData` class (an `N(K)`-stable equipollence class
  of valuations of the root datum satisfying V 0–V 5 of KP Definition 6.1.2),
  a representing centralizer datum for `Z = Z_G(S)`, and V 6 for all of
  `Z(K)` on that class;
- every `E : UnramifiedZeroDatum F G_K`: a maximally split maximal torus `T`
  of `G_K`, a finite Galois splitting field `L ⊆ F^sep` of `T`, and a simply
  connected cover of the derived subgroup. Its `E.zeroPoints` is the join
  `G(K)^♮ ⊔ T(K)^0` of KP Definition 2.6.23(1);
- every `g` in the rational points `G(K)` of `G_K`;
- every two subsets `Ωa` and `Ωa'` of `C.Apartment`.

It has five hypotheses, in this order:

1. `Ωa` is nonempty;
2. `Ωa` is bounded: every real affine map `f : C.Apartment →ᵃ[ℝ] ℝ` is
   bounded above on `Ωa`;
3. `Ωa'` is nonempty;
4. `Ωa'` is bounded in the same sense;
5. for every `ψ ∈ C.affineRoots`, `ψ` is nonnegative on all of `Ωa` if and
   only if it is nonnegative on all of `Ωa'`.

The conclusion is the equality of subgroups of `G(K)`

```lean
E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) =
  E.zeroPoints ⊓ C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa')
```

Here `C.apartmentMap : C.Apartment → C.ReducedBuilding` is `x ↦ [(1, x)]`,
`C.ReducedBuilding` is the quotient (7.6.2) of `G(K) × A`, and
`C.pointwiseFixer Y` is the pointwise fixer in `G(K)` of `Y ⊆ C.ReducedBuilding`.
The set `(fun x => g • C.apartmentMap x) '' Ω` is the translate `g · Ω` of
`Ω` into the apartment `g · A`. In words: the pointwise fixer in `G(K)^0` of a
nonempty bounded subset of a translated apartment depends only on which
affine roots are nonnegative on the subset.

The apartment is an affine space over the finite-dimensional real vector
space `V(S)/V(S)^Φ` (KP's `V(S′)`). Hence hypotheses 2 and 4 say exactly that
the sets are bounded in the sense of KP: if every affine function is bounded
above, then so is its negative, and the coordinates are bounded.

## Source

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, read
with the authors' corrections of 1 November 2024
(`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`).

### The setting of KP Chapter 7

Chapter 7 (printed p. 235 / PDF p. 266) works over a Henselian field `k`
with a discrete valuation `ω` with `ω(k^×) = ℤ`, a connected reductive
`k`-group `G` with a maximal split torus `S`, and an equipollence class
`A(S)` of valuations of the root datum (Definitions 6.1.2 and 6.1.7) with the
`N(k)`-action of 6.1.8 satisfying Axiom 4.1.4. The correction on PDF p. 33
adds Axiom 4.1.6 AS 5, which is known for quasi-split `G` (Propositions
6.3.13 and 6.6.2). The correction on PDF p. 25 requires `k` Henselian with
perfect residue field for §2.6(e), which contains Definition 2.6.23 and
Lemma 2.6.24.

Here `k = K`. It is Henselian and discretely valued, as an algebraic
extension of the complete field `F`. Its normalized valuation has value group
`ℤ` because `K/F` is unramified, and its residue field is an algebraic
closure of the finite residue field of `F`, hence perfect. `G_K` is connected
reductive by the data of `C`, and quasi-split by KP Corollary 2.3.8
(printed p. 81 / PDF p. 112). The class
of `C` consists of `ω`-compatible valuations (V 6 is part of `C`), so by KP
Proposition 6.2.6 (printed p. 216 / PDF p. 247) it is the canonical class of
Definition 6.1.27. It therefore satisfies all hypotheses of Chapter 7,
including AS 5 and V 7. So the statement adds no hypothesis to the source; it
needs none beyond what `C` already supplies.

### Definitions and results used

- **Definition 6.3.4** (printed p. 218 / PDF p. 249). `Ψ` is the set of
  affine functionals `ψ` on `A` whose derivative `ψ̇` is a root and with
  `U_ψ ⊈ U_{ψ+} · U_{2ψ̇}(k)`. The Library's `C.affineRoots` is exactly this
  set for the class of `C`, with `U_ψ` and `U_{ψ+}` of Definition 6.3.1 and
  `U_{2a}(k) = 1` when `2a` is not a root. Hypothesis 5 quantifies over this
  `Ψ`, not over the larger set `Ψ′` of Definition 6.3.4 and not over all
  affine functionals. Both the derivative of `ψ` and the group `U_ψ` are
  determined by `ψ` alone.
- **Definition 7.4.1** (printed p. 255 / PDF p. 286). For a nonempty
  `Ω ⊂ A`, `U_{a,Ω,0} = ⋂_{x∈Ω} U_{a,x,0}`; `G(k)^♯_Ω` is generated by the
  `U_{a,Ω,0}` for all `a ∈ Φ`; and `G(k)^0_Ω = Z(k)^0 · G(k)^♯_Ω`, with
  `Z(k)^0` of Definition 2.6.23 for `Z = Z_G(S)`.
- **Lemma 7.4.4(3)** (printed p. 256 / PDF p. 287). `G(k)^♯_Ω` is the
  subgroup generated by the `U_ψ` for all `ψ ∈ Ψ` with `ψ(Ω) ≥ 0`, that is,
  `ψ(x) ≥ 0` for every `x ∈ Ω`. The corrections change only the notation of
  part (2) of this lemma.
- **Proposition 7.7.5(1)** (printed p. 269 / PDF p. 300). For a nonempty
  bounded `Ω ⊂ A`, `G(k)^0_Ω` is the pointwise stabilizer of `Ω` in `G(k)^0`
  for the action of `G(k)` on the building `B(G)`.
- **Remark 7.6.5** (printed p. 266 / PDF p. 297). A geometric realization
  of `B(G)`, compatible with the action of `G_ad(k)` and hence of `G(k)`, is
  the quotient of `G(k) × A` by (7.6.2), with
  `A ⊂ B(G)` as `x ↦ [(1, x)]`. This is the Library's `C.ReducedBuilding`
  and `C.apartmentMap`.
- **Definition 2.6.23(1) and Lemma 2.6.24** (printed p. 104 / PDF
  p. 135). For quasi-split `G`, `G(k)^0 = G(k)^♮ · T(k)^0` for a
  maximally split maximal torus `T`, with `T(k)^0` of Definition 2.5.13.
  Lemma 2.6.24: this does not depend on the choice of `T`, and `G(k)^0` is
  normal and open in `G(k)`.

## Why the source results give the statement

**The case `g = 1`.** Let `Ω` be `Ωa` or `Ωa'`. By Definition 7.4.1(4),
`G(K)^0_Ω = Z(K)^0 · G(K)^♯_Ω`, and `Z(K)^0` does not depend on `Ω`. By
Lemma 7.4.4(3), `G(K)^♯_Ω` is generated by the `U_ψ` with `ψ` in the set
`{ψ ∈ Ψ | ψ(Ω) ≥ 0}`. Hypothesis 5 says that this set is the same for `Ωa`
and `Ωa'`. Hence `G(K)^♯_{Ωa} = G(K)^♯_{Ωa'}` and
`G(K)^0_{Ωa} = G(K)^0_{Ωa'}`. Both sets are nonempty and bounded
(hypotheses 1–4), so Proposition 7.7.5(1) identifies `G(K)^0_Ω` with the
pointwise stabilizer of `Ω` in `G(K)^0`. Via Remark 7.6.5 this stabilizer
is `G(K)^0 ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)`. Therefore

```
G(K)^0 ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa) =
  G(K)^0 ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa').
```

**Translation by `g`.** For `Y = C.apartmentMap '' Ω`, the set
`(fun x => g • C.apartmentMap x) '' Ω` is `g • Y`. Its pointwise fixer is
`g · C.pointwiseFixer Y · g⁻¹`. Since `G(K)^0` is normal in `G(K)`
(Lemma 2.6.24),
`G(K)^0 ⊓ g P g⁻¹ = g (G(K)^0 ⊓ P) g⁻¹` for every subgroup `P`.
Conjugating the equality for `g = 1` by `g` gives the equality for `g`.

**Every datum `E`.** Each `E` consists of the choices KP's definition
allows: a maximally split maximal torus `T = E.T`, a finite Galois extension
`L/K` splitting `T`, and a simply connected cover of the derived subgroup.
`E.torusIwahori` is `T(K)^0` of Definition 2.5.13, which does not depend on
`L` (KP Lemma 2.5.12 and Definition 2.5.13, printed pp. 89–90 / PDF
pp. 120–121). The image of `G_sc(K) → G(K)` is `G(K)^♮`
(Definition 2.6.20), which does not depend on the chosen cover, since any
two are isomorphic over the derived subgroup. The product `G(K)^♮ · T(K)^0`
is a subgroup, so it equals the join used by `E.zeroPoints`. Thus
`E.zeroPoints = G(K)^0` by Definition 2.6.23(1). By Lemma 2.6.24 this does
not depend on `T`. In particular it equals `G(K)^♮ · Z(K)^0` for
`T = Z = Z_G(S)` of `C`, which is a maximally split maximal torus because
`G_K` is quasi-split. That is the group in Definition 7.4.1 and
Proposition 7.7.5. So quantifying over every `E` adds nothing to the
single-group statement; `E` need not be related to `S`. The independence is
the separate Library statement `UnramifiedZeroPointsIndependenceStatement`.

## Provenance

The statement is derived, not quoted. KP state its ingredients separately:
Definition 7.4.1, Lemma 7.4.4(3) and Proposition 7.7.5(1) for `g = 1` and
`k = K`, and Lemma 2.6.24 for normality and for the independence of the
choices in `E`. The statement combines them on the Library's existing data
(`MaximalUnramified.BuildingData`, `UnramifiedZeroDatum`), adds the
translation by `g ∈ G(K)`, and phrases "the same affine roots nonnegative
on `Ω`" as hypothesis 5. The argument above derives this combination.

## Choices and scope

- Hypothesis 5 compares affine roots in `Ψ = C.affineRoots`, as Lemma
  7.4.4(3) does, not the larger `Ψ′`.
- Both subsets are required to be nonempty and bounded, because Definition
  7.4.1 and Proposition 7.7.5(1) are stated for such sets.
- The statement concerns fixers in `G(K)^0` only. It says nothing about
  fixers in `G(K)^b`, `G(K)^1` or `G(K)`; the argument uses the generation
  of `G(K)^0_Ω` by `Z(K)^0` and affine root groups.
- It is stated over `K`, not over `F`. Comparison over `F` belongs to the
  consumers below.

## Intended consumers

The construction of the integral models for KP Axiom 4.1.20 (Task 5429,
`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`) builds neutral models over the
integers of `K` whose integral points are
`E.zeroPoints ⊓ C.pointwiseFixer (g · Ω)` (statement Task 5851). It
compares these models through their points over the integers of `K`. The
consumer plans to use this statement for the two neutral-model equalities of
Axiom 4.1.20:

- part (2), closure invariance: an affine root composed with the affine
  apartment map is continuous, so it is nonnegative on a set if and only if
  it is nonnegative on its closure;
- part (1), facet constancy: by the facet clause of
  `UnramifiedApartmentDescentStatement` (statement Task 5877), a facet of the
  apartment of `G` maps into one facet of `C.Apartment`, on which every
  affine root has constant sign.

These uses are the consumer's arguments; this module asserts neither.
