# Reduction of the dynamic case of C.1.6 to corepresented groups

Authors: Worker 254, Worker 266.

This module reduces the dynamic pseudo-reductive case of CGP Proposition
C.1.6, the proposition `DynamicParabolicQuotientDVRLifting k` of
`Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase`, to groups given
by an explicit coordinate algebra. Every affine group scheme `G` over a field
`k` is isomorphic to such a group. The module transports the data along this
isomorphism. Everything lives in the namespace `Langlands.GroupScheme`.

The step is a change of presentation and has no counterpart in CGP. It lets
Worker 266's core argument work with the coordinate algebra `B` directly. The
spectra `Corepresented.algOver k A` (`Spec A` as a `k`-scheme) and the maps
`Corepresented.algOverHom φ` (the morphism of spectra given by a `k`-algebra
map `φ`) come from Worker 266's module
`Langlands.GroupScheme.Dynamic.FieldPointBasicOpen`.

## Definition

`CorepresentedDynamicParabolicQuotientDVRLifting k` says the following. Take
a group-valued functor `F` on `k`-algebras, corepresented by the `k`-algebra
`B` via `e`, and let `G = Corepresented.groupScheme F e` (so `G.X = Spec B`).
Take a cocharacter `χ : 𝔾_m ⟶ G` and a morphism `q : G.X ⟶ Q` of
`k`-schemes. Assume that `G` is pseudo-reductive, that `q.left` is smooth,
surjective and quasi-compact, and that on every test scheme `T` over `k`, two
points `g, h` of `G` satisfy `g ≫ q = h ≫ q` exactly when `g⁻¹ * h` lies in
`Dynamic.parabolic χ`. Then for every discrete valuation ring `R` in
`Type u` that is a `k`-algebra with geometrically reduced residue field over
`k`, every morphism `x : algOver k (Frac R) ⟶ Q` over `k` factors as
`algOverHom (R → Frac R) ≫ xR` for some `xR : algOver k R ⟶ Q`.

These are the hypotheses of `DynamicParabolicQuotientDVRLifting`, restricted
to corepresented groups. The conclusion is the DVR lifting property
`PseudoComplete.HasDVRLifting Q`, written with `algOver` and `algOverHom`.

## Main results

- `dynamicParabolicQuotientDVRLifting_of_corepresented`: if
  `CorepresentedDynamicParabolicQuotientDVRLifting k` holds, then
  `DynamicParabolicQuotientDVRLifting k` holds, for every field `k : Type u`.
- `PseudoComplete.genericPoint_eq_algOverHom`: the generic-point map
  `PseudoComplete.genericPoint R`, viewed as a map
  `algOver k (Frac R) ⟶ algOver k R`, equals
  `algOverHom (IsScalarTower.toAlgHom k R (FractionRing R))`.
- `Corepresented.algebraFiniteType_of_locallyOfFiniteType`: if the structure
  morphism of `Corepresented.groupScheme F e` is locally of finite type, then
  `B` is a finite type `k`-algebra.
- `Corepresented.algebraFiniteType_of_isPseudoReductive`: if
  `Corepresented.groupScheme F e` is pseudo-reductive, then `B` is a finite
  type `k`-algebra.

The `Flat q.left` instance that the core argument also needs comes from
`Smooth q.left` through Mathlib's instance `Smooth f → Flat f`, so the module
adds no lemma for it.

## Proof

Finite type. The structure morphism of `Corepresented.groupScheme F e` is, by
definition, `Spec.map` of the algebra map `k → B`. By
`HasRingHomProperty.Spec_iff`, it is locally of finite type exactly when that
ring map is of finite type, that is, when `B` is a finite type `k`-algebra.
A pseudo-reductive group is smooth over `k`, hence locally of finite type.

Generic point. Both morphisms have underlying scheme map
`Spec.map (R → Frac R)`, and the source and target objects agree up to
unfolding definitions. `Over.OverMorphism.ext rfl` closes the goal.

Reduction. Let `G`, `χ`, `q` satisfy the hypotheses of
`DynamicParabolicQuotientDVRLifting k`. Since `G` is pseudo-reductive, its
structure morphism is affine, so `G.X.left` is affine. Let
`e := AffineCoordinates.groupSchemeIso G`, from the corepresented group `G₀`
of the chosen coordinate algebra of `G` to `G`. Set
`χ₀ := Dynamic.Affine.cocharacter χ`, which is `χ ≫ e.inv`, and
`q₀ := e.hom ≫ q`.

- `G₀` is pseudo-reductive by `IsPseudoReductive.of_iso e`.
- `q₀.left` is the composite of the isomorphism underlying `e.hom`
  (`isIso_left_of_iso`) with `q.left`, so it is smooth, surjective and
  quasi-compact.
- Fibres. `Dynamic.parabolic_eq_comap_of_iso χ₀ e` gives
  `P(χ₀) = e⁻¹ P(χ₀ ≫ e.hom)`, and `χ₀ ≫ e.hom = χ`. So `g⁻¹ * h ∈ P(χ₀)`
  says `(g⁻¹ * h) ≫ e.hom ∈ P(χ)`. Since `e.hom` is a homomorphism, this is
  `(g ≫ e.hom)⁻¹ * (h ≫ e.hom) ∈ P(χ)` (`MonObj.mul_comp`,
  `GrpObj.inv_comp`). By the fibre hypothesis on `q`, that is equivalent to
  `g ≫ q₀ = h ≫ q₀`.

Applying `CorepresentedDynamicParabolicQuotientDVRLifting k` to `G₀`, `χ₀`
and `q₀` gives, for every point `x` of `Q` over `Frac R`, an extension `xR`
over `R` with `algOverHom (R → Frac R) ≫ xR = x`. The object
`PseudoComplete.algebraSpec k A` equals `algOver k A` up to unfolding
definitions, so `x` can be used as is. By `genericPoint_eq_algOverHom`, the
extension satisfies `genericPoint R ≫ xR = x`, which is the DVR lifting
property of `Q`.

## Dependencies

The module imports Worker 266's modules
`Langlands.GroupScheme.PseudoParabolicQuotientDynamicCase` and
`Langlands.GroupScheme.Dynamic.FieldPointBasicOpen`, which are not yet in the
Library. It also imports the Library modules
`Langlands.GroupScheme.Dynamic.AffineRepresentability` and
`Langlands.GroupScheme.Reductive.GeneralLinear`.
