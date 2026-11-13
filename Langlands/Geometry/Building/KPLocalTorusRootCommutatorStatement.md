# Positive-depth torus points move root-group filtrations over `K = F^ur`

Lean module: `Langlands.Geometry.Building.KPLocalTorusRootCommutatorStatement`.
Declaration: `Langlands.Geometry.Building.KPLocalTorusRootCommutatorStatement`, a
`Prop`-valued definition. This unit states a proposition and proves nothing.

It is the positive-depth input for clause 2 (root compatibility) of S1 (Task 5890), the
`K`-level copy of KP Lemma 7.2.3. Worker 119 drafted the first form of this statement, and
the case computation below, in the Task 5552 shared draft (revision 3,
`KPLocalTorusRootCommutatorStatement`). That draft used a torus `T`, `hT : IsTorus T.toGrp`
and an isomorphism `e : T.toGrp ≅ B.centralizer.Z`. This unit uses D1's binder convention
instead.

## Setting

- `F : Type u`, in an arbitrary universe and of arbitrary characteristic, with `Field F`,
  `ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`.
- `K = UnramifiedClosure F`, the maximal unramified extension, and
  `H : GroupScheme (Spec K)` with `[IsAffineHom H.X.hom]`.
- `B : MaximalUnramified.BuildingData F H`, that is
  `IntegerValuationBuildingData (MaximalUnramified.valuation F) H`. It consists of the
  connected reductive structure of `H`, a maximal `K`-split torus `B.i : S → H`, the
  apartment class `B.apartment` of valuations of the root datum (V 0–V 5 of KP
  Definition 6.1.2), the centralizer datum `B.centralizer` of `Z = Z_H(S)` with its closed
  inclusion `j = B.centralizer.j`, and axiom V 6 for all of `Z(K)`
  (`B.isOmegaCompatible`).
- `hZ : IsTorus B.centralizer.Z`. This is the single binder of D1 (Task 5875, module
  `Langlands.Geometry.Building.KPLocalMoyPrasadGroups`). D1 writes `Z` as the commutative
  group scheme `B.centralizerTorus hZ`, whose underlying group is `B.centralizer.Z`
  definitionally and whose commutativity is `hZ.isCommMonObj`. S1 (Task 5890) uses the same
  convention. Since `Z` is a torus, the minimal parabolic subgroups of `H` are Borel
  subgroups, so `H` is quasi-split over `K` (KP §7.2: "When G is quasi-split, then
  Z = T is a maximal torus").

No binder supplies a parametrization of root groups, a Chevalley–Steinberg system, a
filtration or the conclusion, and there is no Prop premise except `0 < r`.

## Statement

For all such `F`, `H`, `B` and `hZ`, every point `x : B.Apartment`, every relative root
`a : relativeRoots B.i` (multipliable and divisible roots included), and all `r s : ℝ≥0`
with `0 < r`: if

- `t ∈ localGeometricCharacterCongruence F (B.centralizerTorus hZ) r`, and
- `u ∈ B.filtration x a s`, the group `U_{a,x,s} = {u ∈ U_a(K) | x_a(u) ≥ s}`,

then, with `z = rationalPoints.map B.centralizer.j t` the image of `t` in `H(K)`,

`z * u * z⁻¹ * u⁻¹ ∈ B.apartment.filtrationBlock x (fun _ => ((r + s : ℝ≥0) : ℝ)) a`.

### The hypothesis on `t`

`localGeometricCharacterCongruence F T r` (module `KPLocalTorusCharacterFiltration`) is the
set of `t ∈ T(K)` such that, for every character `χ` of the base change of `T` to
`Ω = SeparableClosure F`, `χ(t)` is a unit with `ω(χ(t)) = 0` and `r ≤ ω(χ(t) - 1)`. Here
`ω = algebraicExtensionAddValuation F Ω`. Since `Ω` is separably closed, these `χ` are all
characters of the torus `Z`, and in particular all absolute roots of `H` with respect to `Z`.

`ω` is normalized so that a uniformizer of `F` has value `1`
(`algebraicExtensionAddValuation_base_unit`). The apartment of `B` uses the integer order of
`MaximalUnramified.valuation F`, which agrees with the order of `F` on `F`
(`MaximalUnramified.order_base_eq_localFieldOrder`). Since `K/F` is unramified, the depth `r`
of the congruence condition and the depths of the root-group filtrations are measured on
the same scale.

At depth `r > 0`, D1's `Z(K)_r = B.centralizerTorusFiltration hZ r` is the published
`localTorusFiltration F (B.centralizerTorus hZ) hZ r`. By definition
(`localTorusFiltrationAtSplitting`) it is the norm Iwahori subgroup intersected with
`localGeometricCharacterCongruence F (B.centralizerTorus hZ) r`. So it lies in the
congruence subgroup. The hypothesis of this statement is therefore weaker than membership in
`Z(K)_r`, and the statement applies to every element of `Z(K)_r`.

### The conclusion

`B.apartment.filtrationBlock x f a` (module `FilteredRootProducts`) is the set of products
`v * w` with `v ∈ B.filtration x a (f a)` and `w ∈` the doubled-root filtration
`doubleFiltration x a (f (2 • a))`. At the constant function `f = r + s` this is the block

`U_{a,x,r+s} · U_{2a,x,r+s}`

of KP Definition 7.3.3(1), with the convention `U_{2a} = {1}` when `2a` is not a root (KP
Remark 7.3.4). The conclusion has the shape of
`ParahoricBuildingData.CentralizerFiltration.IsRootCompatible` (module
`KPMoyPrasadFiltration`), with `B` in place of `P`.

## Provenance

KP do not state this as a separate result. It is the root-compatibility property of the
torus filtration. The provenance paragraph in the Markdown of `IsRootCompatible`
(`KPMoyPrasadFiltration.md`) explains that this property is derived, not stated in the
source, and why the block and not `U_{a,x,r+s}` alone is needed. Here it is stated over `K`,
where `H` is quasi-split and `Z` is a torus, for the congruence condition that defines
`Z(K)_r` at positive depth. The sources of the argument below are:

- KP §7.2 and Lemma 7.2.3. The proof of the lemma reduces commutators in the rank-one group
  generated by `U_{±a}` and `U_{±2a}` to the computations in `SL_2` and `SU_3` from the proof
  of Proposition 7.1.1 for quasi-split groups. In those computations the torus acts on root
  groups through absolute roots.
- KP Definition 7.3.3(1) and Remark 7.3.4 for the block `U_{a,x,f}`.
- KP Construction 6.1.17, Proposition 6.1.19 and Definition 6.1.20 (Chevalley valuations of
  quasi-split groups, which are `ω`-compatible), and Proposition 6.2.6 (any two
  `ω`-compatible valuations are equipollent).
- KP (2.7.2) for the root group of `SU_3` and its group law.

## Why the statement should hold

This is an explanation, not a proof. The Library does not yet identify the valuation of `B`
with a Chevalley–Steinberg valuation.

**Reduction to Chevalley–Steinberg coordinates.** Every valuation in `B.apartment` satisfies
V 0–V 5 and V 6, so it is `ω`-compatible. A Chevalley valuation of the quasi-split group
`H_K` is `ω`-compatible (KP Proposition 6.1.19). By KP Proposition 6.2.6 the two are
equipollent. So the point `x` is a Chevalley valuation `φ` translated by some `v ∈ V(S)`,
and `x_a = φ_a + a(v)` on `U_a(K)`, `x_{2a} = φ_{2a} + 2a(v)` on `U_{2a}(K)`. The translation
adds the same constant to both sides of each bound below, so it suffices to take `x = φ`.

`φ` comes from a Chevalley–Steinberg system (KP Construction 6.1.17). Let `ã` be an absolute
root restricting to `a` (to `b` when `a = 2b` is divisible), with field of definition `L`,
and let `σ` be the nontrivial automorphism of the quadratic extension in the multipliable
case. `ω` extends uniquely to `L`, so `ω ∘ σ = ω`. Put `c = ã(t) ∈ L` and `δ = c - 1`. Then
`ω(δ) ≥ r` and `ω(σ(c) - 1) = ω(σ(δ)) ≥ r`, because `ã` and `σ(ã)` are characters of `Z`
over `Ω`. Conjugation by `t` acts on the coordinates through these absolute roots.

**`a` neither multipliable nor divisible (type R1, the `SL_2` case).** `U_a(K) ≅ L` through
`x_a`, with `φ_a(x_a(α)) = ω(α)` and `t x_a(α) t⁻¹ = x_a(cα)`. The commutator is
`x_a(δα)`, and `ω(δα) ≥ r + ω(α) ≥ r + s`. So it lies in `U_{a,x,r+s}`, and `2a` is not a
root.

**`a` divisible, `a = 2b` (type R3).** `U_a(K) = {x_b(0, β) | β + σ(β) = 0}`, with
`φ_a(x_b(0, β)) = ω(β)`. The torus acts on `β` through the absolute root `ã + σ(ã)`, by
`cσ(c)`. The commutator is `x_b(0, (cσ(c) - 1)β)`. Since `cσ(c)` is a character value,
`ω(cσ(c) - 1) ≥ r`. So the commutator lies in `U_{a,x,r+s}`, and `2a = 4b` is not a root.

**`a` multipliable (type R2, the `SU_3` case).** `U_a(K) = {x(α, β) | β + σ(β) = ασ(α)}` with
the group law `x(α₁, β₁) x(α₂, β₂) = x(α₁ + α₂, β₁ + β₂ + σ(α₁)α₂)` (KP (2.7.2)),
inverse `x(α, β)⁻¹ = x(-α, σ(β))`, `φ_a(x(α, β)) = ω(β)/2`, `U_{2a}(K) = {x(0, β)}` and
`φ_{2a}(x(0, β)) = ω(β)`. The torus acts by `t x(α, β) t⁻¹ = x(cα, cσ(c)β)`. Using
`σ(α)α = β + σ(β)`, the commutator is

`t u t⁻¹ u⁻¹ = x(δα, σ(c)δβ - σ(δ)σ(β))`.

It factors as

`x(δα, σ(c)δβ - σ(δ)σ(β)) = x(δα, δσ(δ)β) · x(0, δβ - σ(δ)σ(β))`,

because `σ(c) - σ(δ) = 1`. Both factors are points of the root groups:
`δσ(δ)β + σ(δσ(δ)β) = δσ(δ)ασ(α)`, and `δβ - σ(δ)σ(β)` has trace `0`.

- The first factor lies in `U_{a,x,r+s}`: `ω(δσ(δ)β)/2 = ω(δ) + ω(β)/2 ≥ r + s`.
- The second lies in `U_{2a,x,r+s}`: `ω(δβ - σ(δ)σ(β)) ≥ r + ω(β) ≥ r + 2s ≥ r + s`.
  The last step uses `s ≥ 0`.

**Why the block is needed.** In the multipliable case the commutator itself gains only
`r/2` in `x_a`. For `u = x(0, β) ∈ U_{2a}(K)` the commutator is `x(0, (cσ(c) - 1)β)`, and
`x_a` of it is `ω(cσ(c) - 1)/2 + ω(β)/2`. This can equal `r/2 + s`, so the commutator need
not lie in `U_{a,x,r+s}`. It gains the full `r` in `x_{2a}`, which puts it in
`U_{2a,x,r+s}`. This is the reason given in the provenance paragraph of `IsRootCompatible`.

**Why `0 < r`.** Depth `0` does not need the coordinates; it is proved from V 6 (see the
next section). At positive depth, the axioms of `IntegerValuationBuildingData` control only
`ω(χ(z))`, not `ω(χ(z) - 1)`, so the gain of `r` needs the root-group coordinates above.

## Use: clause 2 of S1

Clause 2 of S1 says: for `z ∈ j(Z(K)_r)` and `u ∈ U_{a,x,s}`,
`z u z⁻¹ u⁻¹ ∈ U_{a,x,r+s} U_{2a,x,r+s}`. It follows from this statement together with the
depth-`0` case.

- `r = 0`: `Z(K)_0` lies in the character valuation kernel
  (`centralizerTorusFiltration_le_characterValuationKernel` in D1). By V 6 such points fix
  the apartment, so conjugation by `z` preserves `U_{a,x,s}`. Then
  `z u z⁻¹ u⁻¹ ∈ U_{a,x,s}`, and it equals `(z u z⁻¹ u⁻¹) · 1` in the block.
- `r > 0`: `Z(K)_r` lies in the congruence subgroup (see above), and this statement applies.

Worker 119's Task 5552 draft (revision 3, `KPLocalCentralizerFiltrationRootCompatible`)
carries out this derivation in the `T`, `hT`, `e` form of the statement. In D1's
convention, take `T = B.centralizerTorus hZ` and `e = Iso.refl _`
(`centralizerTorusFiltration_eq_map_iso` in D1).

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`):

- §7.2, Lemma 7.2.3 and its proof: printed pp.245–246, PDF pp.276–277;
- Definition 7.3.3(1) and Remark 7.3.4: printed p.247, PDF p.278;
- the `SL_2` and `SU_3` computations in the proof of Proposition 7.1.1 for quasi-split `G`:
  printed pp.239–240, PDF pp.270–271;
- Definition 6.1.2 (V 0–V 6): printed p.199, PDF p.230;
- Construction 6.1.17, Proposition 6.1.19, Definition 6.1.20: printed pp.205–207, PDF
  pp.236–238;
- Proposition 6.2.6: printed p.216, PDF p.247;
- (2.7.2), the root group of `SU_3` and its group law: printed p.110, PDF p.141.
