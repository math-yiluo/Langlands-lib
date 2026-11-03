# Proof that orbit maps onto reduced homogeneous schemes are faithfully flat

Author: Worker 716. The published statement was written by Worker 716 with
Worker 1293, who designed its interface.

The module proves

```
theorem Langlands.GroupScheme.orbitMapFaithfullyFlat :
    OrbitMapFaithfullyFlatStatement.{u}
```

for the published proposition of `Langlands.GroupScheme.OrbitMapFlatStatement`,
at arbitrary universe `u`. Fix an algebraically closed field `k`, a group scheme
`G` over `Spec k` that is locally of finite type and quasi-compact, a reduced
scheme `O` locally of finite type over `k`, an action `a : SchemeAction G O`
and a rational point `x` of `O`. Assume every rational point of `O` is `g • x`
for a rational point `g` of `G`. Write `π` for the orbit map
`a.act (𝟙 G.X) (toUnit G.X ≫ x)`. The proof shows that `π.left` is flat,
surjective and quasi-compact.

## Generic flatness (namespace `Langlands.GroupScheme.OrbitMapFlat`)

- `exists_flat_awayMap`: let `φ : R →+* B` be of finite type, with `R` a
  noetherian domain. Then some `a ≠ 0` in `R` makes
  `Localization.awayMap φ b : R_b →+* B_b` flat for every multiple `b` of `a`.
  This restates the Library's
  `Langlands.Algebra.GenericFlatness.genFlat_of_finiteType`, applied to `B` as
  an `R`-module. That result gives flatness over `R` of the localized module
  `LocalizedModule (powers b) B`. The Library's `flat_localizedModule_iff`
  transfers this to the ring `B_b = Localization.Away (φ b)`, which is a
  localization of the `R`-module `B` at the powers of `b`. Mathlib's
  `Module.flat_iff_of_isLocalization` turns flatness over `R` into flatness
  over `R_b`.

## Local flatness data

- `FlatNear f z`: there are opens `U` of the target and `V ∋ z` of the source
  with `V ≤ f⁻¹ U` and the restriction `f.resLE U V` flat.
- `flat_of_forall_flatNear`: if `FlatNear f z` holds at every `z`, then `f` is
  flat. This is Mathlib's `IsZariskiLocalAtSource.iff_exists_resLE` for `Flat`.
- `flatNear_of_comm`: let `φ` and `ψ` be automorphisms of the source and target
  with `φ ≫ f = f ≫ ψ`. If `FlatNear f (φ z)` holds, then `FlatNear f z` holds.
  The witnesses are the opens `ψ⁻¹ U` and `φ⁻¹ V`. Then
  `φ.resLE ≫ f.resLE = (φ ≫ f).resLE = (f ≫ ψ).resLE = f.resLE ≫ ψ.resLE`
  (Mathlib's `resLE_comp_resLE`). The left side is flat because restrictions of
  the isomorphism `φ` are isomorphisms. So `f.resLE (ψ⁻¹ U) (φ⁻¹ V)` is flat
  after cancelling the isomorphism on the right.
- `exists_affineOpen_isDomain`: a reduced locally noetherian scheme with a
  point has a nonempty affine open whose ring of sections is a domain. An
  affine open `V₀` is a noetherian space. Mathlib's
  `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` gives a
  nonempty open inside one irreducible component. Its image in `Y` is an
  irreducible open, and an affine open `V` inside it is irreducible. `V` is
  reduced, so it is integral (`isIntegral_of_irreducibleSpace_of_isReduced`),
  and `Γ(Y, V)` is a domain.
- `exists_open_flatNear`: let `f : X ⟶ Y` be locally of finite type and
  quasi-compact, with `Y` reduced, locally noetherian and nonempty. Then
  `FlatNear f z` holds for every `z` over some nonempty open `U` of `Y`.
  Take `V` from the previous lemma, so `A = Γ(Y, V)` is a noetherian domain.
  Since `f` is quasi-compact, `f⁻¹ V` is covered by finitely many affine opens
  `W`. Each `appLE V W : A ⟶ Γ(X, W)` is of finite type. Choose generic
  elements `a_W` by `exists_flat_awayMap`, and let `b` be their product.
  Then `b ≠ 0`, and `U = D(b)` is nonempty because `V` is integral. A point `z`
  over `U` lies in some `W`. The restriction of `f` to `D(appLE b) ⊆ W` over
  `D(b)` is a map of affine schemes. Its ring map is identified with
  `Localization.awayMap (appLE V W) b` (Mathlib's `appLE_eq_away_map`), which is
  flat because `a_W ∣ b`.

## Translations by rational points

For a point `g : 𝟙_ ⟶ G.X` over the base:

- `leftMul g = (toUnit G.X ≫ g) * 𝟙 G.X : G.X ⟶ G.X`, left multiplication by
  `g`;
- `actBy a g = a.act (toUnit O ≫ g) (𝟙 O) : O ⟶ O`, the action of `g`.

`leftMul_comp_leftMul`, `leftMul_one`, `actBy_comp_actBy` and `actBy_one` give
`leftMul g ≫ leftMul h = leftMul (h * g)` and the analogous law for `actBy`.
They follow from Mathlib's `comp_mul`, the group laws, and the Library's
`SchemeAction.naturality`, `act_mul` and `act_one`. Hence both maps are
isomorphisms, with inverses given by `g⁻¹`.

- `leftMul_comp_orbit`: `leftMul g ≫ π = π ≫ actBy a g`. Both sides equal
  `h ↦ (g * h) • x`, by naturality and `act_mul`.
- `comp_actBy`: for a rational point `y`, `y ≫ actBy a g = a.act g y`.
- `comp_orbit`: for a rational point `g`, `g ≫ π = a.act g x`.

## Main theorem

Instances. `O` is locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`)
and Jacobson (`LocallyOfFiniteType.jacobsonSpace`). Its underlying space is
quasi-separated, so `O.hom` is quasi-separated because the base is affine. Since
`π.left ≫ O.hom = G.X.hom`, the map `π.left` is locally of finite type
(`locallyOfFiniteType_of_comp`). It is quasi-compact by
`QuasiCompact.of_comp`, using that `G.X.hom` is quasi-compact and `O.hom` is
quasi-separated. This is the quasi-compactness conclusion.

Closed points are in the orbit (`hrat`). A closed point `c` of `O` is a
rational point, by Mathlib's `pointOfClosedPoint` over the algebraically closed
base. By the transitivity hypothesis it is `a.act g x = g ≫ π` for a rational
point `g`. So `c` is the image under `π` of the closed point of `g`.

Generic flatness. `exists_open_flatNear`, applied to `π.left`, gives a nonempty
open `U` of `O` over which `π` is flat near every point.

Translates of `U` cover `O` (`hcover`). Suppose some point `w` is outside
`actBy a g ⁻¹ U` for every rational `g`. The intersection `Z` of the closed sets
`(actBy a g)⁻¹ (O ∖ U)` is closed and contains `w`. Since `O` is Jacobson, `Z`
contains a closed point `c`, and `U` contains a closed point `u`
(`nonempty_inter_closedPoints`). By `hrat`, `c` and `u` are the images of rational
points `g₁` and `g₂` of `G`. Then `actBy a (g₂ * g₁⁻¹)` sends `c` to `u ∈ U`,
because `(g₁ ≫ π) ≫ actBy a (g₂ * g₁⁻¹) = g₂ ≫ π` (by `comp_actBy`,
`comp_orbit` and `act_mul`). This contradicts `c ∈ Z`.

Flatness. For a point `z` of `G`, choose `g` with `actBy a g (π z) ∈ U`. By
`leftMul_comp_orbit`, `π (leftMul g z) = actBy a g (π z)`, which lies in `U`, so
`FlatNear π (leftMul g z)` holds. `flatNear_of_comm` with the automorphisms
`leftMul g` and `actBy a g` gives `FlatNear π z`. Then
`flat_of_forall_flatNear` shows that `π` is flat.

Surjectivity. Let `w` be a point of `O`. The closure of `{w}` is a nonempty
closed set, so it contains a closed point `c` (Jacobson). By `hrat`, `c = π z₀`
for a point `z₀` of `G`. Thus `w ⤳ π z₀`. A flat morphism is generalizing
(Mathlib's `Flat.generalizingMap`), so some `z ⤳ z₀` has `π z = w`.

## Use of the hypotheses

- `IsAlgClosed k`: closed points of `O` are rational (`pointOfClosedPoint`).
- Finite type of `G`: `π` is locally of finite type (generic flatness) and
  quasi-compact (generic flatness and the quasi-compactness conclusion).
- Reducedness of `O`: the integral affine open of generic flatness.
- Local finite type of `O`: `O` is locally noetherian (the noetherian domain
  for generic flatness, quasi-separatedness) and Jacobson (closed points in
  nonempty locally closed sets).
- Transitivity: `hrat`, used for the covering and for surjectivity.

## Provenance

The route is Milne's proof of Proposition 1.65(a) in J. S. Milne, *Algebraic
Groups* (2017), source `milne-2017-algebraic-groups`, printed pp.26–27, which
Proposition 7.4(a) applies to orbit maps. Milne uses generic flatness over a
nonempty open `U`, then covers the target by translates `gU`. The errata
snapshot `milne-2017-algebraic-groups-errata-2026-11-02` removes "faithfully"
from generic flatness (A.70). The implemented proof uses only flatness over
`U`, and gets surjectivity from transitivity and the generalizing property of
flat maps. Two steps differ from Milne. Generic flatness is the Library's ring
version, applied on an integral affine open and a finite affine cover of its
preimage. The cover uses closed points of the Jacobson scheme `O` and does not
pass through max spectra. This is a proof of the published statement only; it
publishes no new statement.

The left translation used in the proof is the published
`Langlands.GroupScheme.FiniteIndexTransfer.leftMul G g` from
`Absolute.FiniteIndexQuotientProperProof`. Its lift followed by multiplication
is definitionally the product `(toUnit G.X ≫ g) * 𝟙 G.X`. The orbit-map module
reuses this construction for its composition, isomorphism and equivariance
lemmas.
