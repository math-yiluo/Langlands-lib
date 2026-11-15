# Murre's Proposition 2 from its two steps

This module proves `Langlands.AlgebraicGeometry.UnramifiedFunctor.murreLocalToGlobal_of_steps`:

```
MurreLocalToGlobalStepsStatement.{u, v} → MurreLocalToGlobalStatement.{u, v}
```

That is, Murre's Proposition 2 (Bourbaki exp. 294, §2) follows from the two statements of
`Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps`:

* `MurreChartGluingStatement`, Murre's Lemma 3 in the form of SGA 3, XI, Proposition 3.5;
* `MurreNoetherianChartsStatement`, the inductive step of Murre's noetherian induction over
  the spectrum of a noetherian ring, up to the final application of Lemma 3.

The module only derives the proposition from these two inputs. The argument follows Murre's
proof of Proposition 2 (reduction to an affine noetherian base, noetherian induction, and
gluing by Lemma 3). Three of its steps Murre leaves implicit: separatedness of the
representing scheme, its formal unramifiedness, and passing the charts between a base and an
open subscheme of it. They are proved here directly, as described below. All auxiliary
declarations sit in the namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.LocalToGlobal`.

## Notation

For a presheaf `F` on `Over S` and a morphism `g : S' ⟶ S`, `baseChange g F` is
`(Over.map g).op ⋙ F` (the presheaf `F ×_S S'`). `UnramifiedRepresentable F` means that `F` is
represented by an `S`-scheme `q : Y ⟶ S` with `q` separated, locally of finite type and
formally unramified. An element `ξ ∈ F(U)` is regarded as a morphism `U → F`.
`IsMonoElement` and `InfinitesimallyEtaleAt` are the monomorphism and infinitesimal-étaleness
conditions of `MurreLocalToGlobalSteps` (SGA 3, XI 1.6–1.8).

## Section `Basic`: base change of representability

* `unramifiedRepresentable_of_iso`: `UnramifiedRepresentable` is invariant under isomorphism of
  presheaves (`RepresentableBy.ofIso`).
* `baseChangeCompIso g h F : baseChange g (baseChange h F) ≅ baseChange (g ≫ h) F`, from
  `Over.mapComp`.
* `representableByBaseChange`: if `F` is represented by `Over.mk q`, then `baseChange g F` is
  represented by the pullback `(Over.pullback g).obj (Over.mk q)`. The bijection is the
  adjunction `Over.mapPullbackAdj g` composed with the representation of `F`.
* `unramifiedRepresentable_baseChange`: hence `UnramifiedRepresentable` is stable under base
  change, the representing morphism being `pullback.snd q g`. Separatedness and local finite
  type are inherited by Mathlib instances. Formal unramifiedness comes from
  `MorphismProperty.IsStableUnderBaseChange.of_isPullback`.
* `local_baseChange`: the local hypothesis of Proposition 2 (representability of every
  `baseChange (S.fromSpecStalk s) F`) passes to `baseChange g F` for any `g : S' ⟶ S`. For
  `s' ∈ S'`, Mathlib's `Scheme.SpecMap_stalkMap_fromSpecStalk` factors
  `S'.fromSpecStalk s' ≫ g` as `Spec.map (g.stalkMap s') ≫ S.fromSpecStalk (g s')`. Two uses of
  `baseChangeCompIso` and the previous lemma conclude.

## Section `Charts`: universal elements and transport along open immersions

* `isMonoElement_of_representableBy`, `infinitesimallyEtaleAt_of_representableBy`: if
  `e : F.RepresentableBy Y`, the universal element `e.homEquiv (𝟙 Y)` is a monomorphism and is
  infinitesimally étale at every point. Both follow from the bijectivity of `e.homEquiv` and
  `homEquiv_comp`. For étaleness the unique lift of `v` is `e.homEquiv.symm v`.
* `overMapIso`: for a monomorphism `j : S' ⟶ S` and an `S`-morphism
  `h : T ⟶ (Over.map j).obj U'`, the object `T` is isomorphic to the image under `Over.map j`
  of an `S'`-object.
* `isMonoElement_map`: for a monomorphism `j : S' ⟶ S`, if `ξ ∈ (baseChange j F)(U')` is a
  monomorphism for the presheaf `baseChange j F`, it is also one as an element of
  `F((Over.map j).obj U')`. Two `S`-morphisms `h₁, h₂ : T ⟶ U'` give the same `S`-structure
  on `T` (since `j` is mono), so they are `Over.map j` of two `S'`-morphisms (after the
  isomorphism `overMapIso`). The hypothesis then applies.
* `subsingleton_spec_of_isArtinianRing`: the spectrum of a local artinian ring has one point.
* `infinitesimallyEtaleAt_map`: for an open immersion `j : S' ⟶ S`, infinitesimal étaleness
  of `ξ` for `baseChange j F` at `y` implies it for `F`. Given the data `(A, f, J, u₀, v)` over
  `S`, the image of `f : Spec A ⟶ S` is one point, the image of the point of `Spec (A/J)`. That
  point lies in the image of `j` because `u₀` lands in `U'`. Hence `f` factors as `f' ≫ j`
  (`IsOpenImmersion.lift_fac`). Then `u₀` and `v` come from `S'`-data, where the hypothesis
  gives a unique lift. Its image under `Over.map j` is the required unique lift, uniqueness
  using again that `j` is mono. The transport of `v` uses `BaseChange.equiv_apply` and
  `BaseChange.equiv_base` (module `MurreBaseChangeBasic`).

## Section `Separated`: separatedness via the valuative criterion

Murre states that the representing scheme is separated without giving an argument. The proof
here uses the valuative criterion.

* `eq_of_local`: let `F` be represented by `q : Y ⟶ S`, and let `baseChange (S.fromSpecStalk s) F`
  be represented by a separated `qs : Ys ⟶ Spec 𝒪_{S,s}`. Take a valuation ring `R` with
  fraction field `K`, a ring map `φ : 𝒪_{S,s} ⟶ R`, and two morphisms
  `l₁, l₂ : Spec R ⟶ Y` over `Spec.map φ ≫ S.fromSpecStalk s` that agree on `Spec K`. Then
  `l₁ = l₂`. The two representations turn `l₁, l₂` into two `Spec 𝒪_{S,s}`-morphisms
  `Spec R ⟶ Ys` that agree on `Spec K`. They are equal by the uniqueness part of the
  valuative criterion for the separated `qs` (`IsSeparated.valuativeCriterion`).
* `isSeparated_of_local`: if `S` is locally noetherian, `F` is represented by `q` locally of
  finite type, and every local base change is `UnramifiedRepresentable`, then `q` is
  separated. Here `Y` is locally noetherian, so `q` is quasi-separated, and Mathlib's
  `IsSeparated.of_valuativeCriterion` applies. In a valuative square
  `Spec K → Y, Spec R → S`, the map `Spec R ⟶ S` factors through the local scheme at the image
  of the closed point (`Scheme.Spec_stalkClosedPointTo_fromSpecStalk`), and `eq_of_local`
  applies.

## Section `Assemble`: charts give representability

`unramifiedRepresentable_of_charts`: let `S` be locally noetherian, `F` satisfy
`MurreConditions`, and every local base change be `UnramifiedRepresentable`. Let
`ξᵢ ∈ F(Uᵢ)` (index type in `Type u`) be charts, each locally of finite type and formally
unramified over `S`, monomorphic, and infinitesimally étale at every point, such that every
field-valued point factors through some chart. Then `F` is `UnramifiedRepresentable`.
`MurreChartGluingStatement` gives `Y`, `q` locally of finite type, and open immersions
`Uᵢ ⟶ Y` covering `Y`. Separatedness is `isSeparated_of_local`. Formal unramifiedness is
local on the source (`IsZariskiLocalAtSource.of_openCover`, with the instance supplied
explicitly through `HasRingHomProperty.instIsZariskiLocalAtSource`). On the open cover
formed by the `Uᵢ ⟶ Y` (`Scheme.Cover.mkOfCovers`), the composite `Uᵢ ⟶ Y ⟶ S` is the
structure morphism of `Uᵢ`, formally unramified by hypothesis.

## Section `Affine`: the noetherian induction

* `baseChangeIdIso F : baseChange (𝟙 S) F ≅ F`, from `Over.mapId`.
* `unramifiedRepresentable_affine`: Proposition 2 over `Spec R` for a noetherian ring `R`. The
  proof is by well-founded induction (`WellFoundedGT.induction`; ideals of a noetherian ring
  satisfy the ascending chain condition) on an ideal `J` of `R`. The claim for `J` is: for
  every surjective ring map `φ : R ⟶ A` with kernel `J`, `baseChange (Spec.map φ) F` is
  `UnramifiedRepresentable`. This is Proposition 2 over the closed subscheme `V(J)`, Murre's
  noetherian induction on closed subschemes. In the inductive step:
  * `A` is noetherian (`isNoetherianRing_of_surjective`).
  * `G := baseChange (Spec.map φ) F` satisfies the conditions (`murreBaseChange`).
  * `G` satisfies the local hypothesis (`local_baseChange`).
  * For an ideal `I ≠ 0` of `A`, `baseChange (Spec (A/I) ⟶ Spec A) G` is the base change of
    `F` along the surjection `R ⟶ A/I`. Its kernel `φ⁻¹(I)` strictly contains
    `J = φ⁻¹(0)`, since `Ideal.comap φ` is injective for surjective `φ`. So the induction
    hypothesis applies.

  `MurreNoetherianChartsStatement` then gives charts for `G` over `Spec A`, and
  `unramifiedRepresentable_of_charts` concludes. The case `J = 0`, `φ = 𝟙 R` gives the claim
  for `F` (via `Spec.map_id` and `baseChangeIdIso`).

## Section `General` and the main theorem

`unramifiedRepresentable_general`: Proposition 2 over a locally noetherian `S`. Take Mathlib's
affine open cover `S.affineOpenCover`, with index type `S : Type u` and pieces `Spec Rⱼ`
(`Rⱼ` noetherian by `isLocallyNoetherian_of_isOpenImmersion` and `isLocallyNoetherian_Spec`).
By `unramifiedRepresentable_affine` (with `murreBaseChange` and `local_baseChange`), each
`baseChange (fⱼ : Spec Rⱼ ⟶ S) F` is represented by some `qⱼ : Yⱼ ⟶ Spec Rⱼ`. The charts of
`F` are `Uⱼ := Yⱼ → Spec Rⱼ → S` with the universal elements `ξⱼ`. They are:

* locally of finite type and formally unramified: composites with an open immersion
  (`MorphismProperty.comp_mem`);
* monomorphic and infinitesimally étale: Section `Charts`;
* covering: a field-valued point `g : Spec K ⟶ S` has one-point image, which lies in some
  `Spec Rⱼ`, so `g` factors through `fⱼ` and then through the representing object `Yⱼ`.

`unramifiedRepresentable_of_charts` concludes.

`murreLocalToGlobal_of_steps` applies `unramifiedRepresentable_general` to the two components
of `MurreLocalToGlobalStepsStatement`.

## Axioms

`murreLocalToGlobal_of_steps` depends only on `propext`, `Classical.choice` and `Quot.sound`.
