# Gluing isomorphisms with two prescribed restrictions

This module glues actual isomorphisms of scheme modules from local pieces
when each piece must agree with two prescribed restrictions. The setting is
two morphisms of schemes `j₁ : Y₁ ⟶ Y` and `j₂ : Y₂ ⟶ Y` and two
`Y`-modules `M`, `N`. The prescribed data are isomorphisms

- `e₁ : j₁^* M ≅ j₁^* N`, and
- `e₂ : j₂^* M ≅ j₂^* N`,

of ordinary module pullbacks along `j₁` and `j₂`. In the intended use, `Y` is
an infinitesimal thickening glued from two closed pieces. Here, though, the
maps `j₁` and `j₂` are arbitrary and no closedness, nilpotence or field
hypothesis is assumed.

Namespace: `Langlands.Scheme.Modules.TwoLegIsoGluing`.

## The unit-separation hypothesis

`UnitsJointlyInjectiveOnOpens j₁ j₂ : Prop` says the following. Take every
scheme `T` and every open immersion `t : T ⟶ Y`. Then the map sending a unit
`s` of `Γ(T, ⊤)` to the pair

- `Units.map (pullback.snd j₁ t).appTop s`, and
- `Units.map (pullback.snd j₂ t).appTop s`,

is injective. Here `pullback.snd jᵢ t : pullback jᵢ t ⟶ T` is the actual
projection from the fibre product to `T`. So a unit of each open subscheme of
`Y` is determined by its two restrictions to the inverse images of that open.

`unitsJointlyInjectiveOnOpens_of_affine` reduces this hypothesis to affine
opens. Suppose the injectivity statement above holds for every open immersion
`t : T ⟶ Y` with `T` affine. Then `UnitsJointlyInjectiveOnOpens j₁ j₂` holds.
The proof takes two units on an arbitrary open `T` with the same two
restrictions. It restricts them along each chart `v` of `T.affineCover`. It
transports the hypothesis along the canonical map
`pullback jᵢ (v ≫ t) ⟶ pullback jᵢ t`, using `Scheme.Hom.comp_appTop`. The
affine case then makes the two units agree on every chart, so they agree
globally by `Scheme.OpenCover.ext_elem`.

## Uniqueness on one open

The variables `e₁` and `e₂` are fixed as above. Compatibility is the published
predicate `LineBundleIsoDescent.Compatible j e t φ`. It says that on every
commuting square `a ≫ j = b ≫ t`, the ordinary pullbacks of `e` and `φ` agree
up to the published `squarePullbackIso`.

`compatible_unique` has the following hypotheses:

- `hU : UnitsJointlyInjectiveOnOpens j₁ j₂`;
- an open immersion `t : T ⟶ Y`;
- trivializations `τ : t^* M ≅ 𝒪_T` and `σ : t^* N ≅ 𝒪_T`;
- two isomorphisms `φ ψ : t^* M ≅ t^* N`, each compatible with both
  `(j₁, e₁)` and `(j₂, e₂)`.

Its conclusion is `φ = ψ`. In the proof, applying compatibility to the actual
fibre product square shows that `φ` and `ψ` have the same pullback along each
`pullback.snd jᵢ t`. Next, `τ` and `σ` normalize `φ` and `ψ` to
structure-sheaf automorphisms. The published `structureAutScalar` turns these
into units of `Γ(T, ⊤)`. Then `structureAutScalar_pullback` and
`normalizeIso_pullback` identify the restrictions of those units along both
projections. By `hU`, the units are equal. Finally,
`structureAutScalar_injective` and cancellation of `τ` and `σ` give `φ = ψ`.

## Recognizing the prescribed restrictions

`pullback_eq_of_local_compatible` has the following hypotheses:

- a morphism `j : V ⟶ Y` and an isomorphism `e : j^* M ≅ j^* N`;
- an open cover `𝒰` of `Y` and local isomorphisms `E i` over its charts, each
  compatible with `(j, e)`;
- a global isomorphism `E₀ : M ≅ N` whose ordinary pullback along each
  `𝒰.f i` has hom equal to `(E i).hom`.

Its conclusion is `(Scheme.Modules.pullback j).mapIso E₀ = e`. The proof checks
the hom on the pulled-back cover `𝒰.pullback₁ j` using the published
`LineBundleIsoDescent.hom_ext_of_openCover`. On each chart it combines
compatibility for the fibre product square with the published
`squarePullbackIso_naturality`.

## Existence and uniqueness of the glued isomorphism

`existsUnique_iso_of_local` has the following hypotheses:

- `hU : UnitsJointlyInjectiveOnOpens j₁ j₂`;
- an open cover `𝒰 : Y.OpenCover`;
- for each chart, nonempty trivializations of both `(𝒰.f i)^* M` and
  `(𝒰.f i)^* N` by `structureModule (𝒰.X i)`;
- for each chart, the existence of an isomorphism
  `(𝒰.f i)^* M ≅ (𝒰.f i)^* N` compatible with both `(j₁, e₁)` and `(j₂, e₂)`.

It concludes that there is a unique isomorphism `E₀ : M ≅ N` with
`(Scheme.Modules.pullback j₁).mapIso E₀ = e₁` and
`(Scheme.Modules.pullback j₂).mapIso E₀ = e₂`.

The proof works in three steps.

1. Uniqueness: two such global isomorphisms have compatible ordinary
   pullbacks on each chart, by the published `compatible_pullback`.
   `compatible_unique` makes these pullbacks equal, and
   `hom_ext_of_openCover` gives global equality.
2. Gluing: choose the local lifts. On each pairwise overlap, move both lifts
   to the overlap through the published `compIso`. They stay compatible by
   `Compatible.change_base`. The overlap trivializations come from
   `nonempty_trivial_change_base`, so `compatible_unique` makes the two lifts
   agree there. `squarePullbackIso_hom_eq_compIso` rewrites this agreement as
   the cocycle condition of the published `openCoverIsoGluing_of_homGluing`,
   used with `OpenCoverHomGluing.openCoverHomGluing`. That produces a global
   isomorphism restricting to the chosen lifts.
3. Restrictions: `pullback_eq_of_local_compatible` identifies the two
   ordinary pullbacks of the glued isomorphism with `e₁` and `e₂`.

## The glued isomorphism

The section `Glue` keeps all the hypotheses of `existsUnique_iso_of_local`.

- `glueIso : M ≅ N` is the isomorphism chosen from that unique existence
  statement.
- `glueIso_pullback₁` says its ordinary pullback along `j₁` is `e₁`.
- `glueIso_pullback₂` says its ordinary pullback along `j₂` is `e₂`.
- `eq_glueIso` says that every isomorphism `E : M ≅ N` whose ordinary
  pullbacks along `j₁` and `j₂` are `e₁` and `e₂` equals `glueIso`.

## Provenance

This is an internal derived construction, not a formalization of one cited
source theorem. It is the standard sheaf-theoretic argument: a map is
determined locally, and local lifts that are unique on overlaps glue. It is
assembled from published Library interfaces:

- open-cover isomorphism gluing (`OpenCoverIsoGluing`, `OpenCoverHomGluing`);
- the compatibility API of `LineBundleIsoDescentProof`;
- the normalization of structure-sheaf automorphisms to units
  (`StructureUnitScalars`, `TrivialIsoDescentProof`);
- the change-of-base helpers `compIso`, `nonempty_trivial_change_base` and
  `squarePullbackIso_hom_eq_compIso` (`UnitCocycleDescentUniquenessProof`).

The module does not construct the local lifts, does not prove the
unit-separation hypothesis for any concrete square, and does not prove the
global Picard comparison equivalence.
