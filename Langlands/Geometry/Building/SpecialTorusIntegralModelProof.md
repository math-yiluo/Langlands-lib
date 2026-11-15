# The integral model behind special tori (proof)

This module proves the Library proposition
`Langlands.Geometry.Building.SpecialTorusIntegralModelStatement.{u}` at arbitrary universe `u`,
in equal and mixed characteristic. The statement module
`Langlands.Geometry.Building.SpecialTorusIntegralModelStatement` and its Markdown are
unchanged. The theorem has no premise: there is no extra hypothesis and no supplied building,
point, model or torus.

## Declaration

`Langlands.Geometry.Building.specialTorusIntegralModel : SpecialTorusIntegralModelStatement.{u}`

So for every nonarchimedean local field `F : Type u`, every connected reductive group scheme
`G` over `Spec F` and every maximal split torus `iS : S.toGrp ⟶ G`, there is a smooth
`M : IntegralModel ↥𝒪[F] F G` with connected special fibre, a closed split `𝒪[F]`-torus in `M`
with generic fibre `iS`, and a closed split torus in `M.baseChangeUnramified` whose generic
fibre is a maximal `K`-split torus of `G_K`. Here `K = inertiaFixedField F`. The statement's
Markdown gives the exact form of these four items.

## The implemented proof

The proof is one line. It applies two published Library theorems:

`specialTorusIntegralModelReductionStatement specialTorusBoundedModel`.

1. `Langlands.Geometry.Building.specialTorusBoundedModel :
   SpecialTorusBoundedModelStatement.{u}` (module
   `Langlands.Geometry.Building.SpecialTorusBoundedModelProof`, from Task 6196). It gives a
   smooth `M : IntegralModel ↥𝒪[F] F G` whose base change to `O_K = fixedFieldIntegers F`
   has integral points containing two subgroups. The first is the image of `S_K(K)^1`. The
   second is the image of `A(K)^1` for a maximal `K`-split torus `iA : A.toGrp ⟶ G_K`. Here
   `H(K)^1 = characterValuationKernel (MaximalUnramified.valuation F) H`. Its proof follows
   the first paragraph of the proof of KP Proposition 9.3.4. It takes a point of the building
   of `G_K` fixed by `Gal(K/F)` and by `S(K)^1`, and the smooth full-stabilizer model of that
   point (Axiom 4.1.20). It then descends this model to `𝒪[F]` (§9.2.5). The torus `A` is
   the torus of an apartment through the point.
2. `Langlands.Geometry.Building.specialTorusIntegralModelReductionStatement :
   SpecialTorusIntegralModelReductionStatement.{u}` (module
   `Langlands.Geometry.Building.SpecialTorusIntegralModelReduction`, from Task 5970). The
   proposition `SpecialTorusIntegralModelReductionStatement.{u}` is by definition
   `SpecialTorusBoundedModelStatement.{u} → SpecialTorusIntegralModelStatement.{u}`. So
   applying this theorem to the term in step 1 has exactly the target type. Its proof,
   `specialTorusIntegralModelStatement_of_boundedModel`, does the following.
   * It builds closed split integral tori from the two bounded-point containments
     (`IntegralModel.SplitTorusClosure`). The torus over `𝒪[F]` uses `F ∩ O_K = 𝒪[F]`. The
     torus over `O_K` remains a maximal `K`-split torus after the generic identification.
   * It then passes to the relative identity component
     (`IntegralModel.exists_connected_specialTorusModel`). This gives the connected special
     fibre and keeps smoothness and both tori.

   The Markdown of that module compares this route with KP's schematic closure and
   Proposition B.2.4.

## Source

The target is the building input of the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Proposition 9.3.4 (printed p.332 / PDF p.363). The source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. It is read with the
corrections of 1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`. PDF p.39 of the
corrections revises §9.2.1.

The source passages used are these:

* the Galois-fixed point of the building of `G_K` (corrected §9.2.1);
* Axioms 4.1.1, 4.1.2, 4.1.4 (A1) and 4.1.20 (printed pp.157–159, 163 / PDF pp.188–190, 194);
* the descent of §9.2.5 (printed pp.327–328 / PDF pp.358–359);
* Lemma 2.6.16 (printed p.103 / PDF p.134).

The two input modules use them, and their Markdown records the locators and any departures
from KP's argument. This module adds no mathematics of its own.

## Independence

The proof uses none of `SpecialTorusExistenceStatement`, `UnramifiedSpecialApartmentStatement`
or `ValuationApartmentAxiomsExistenceStatement`, whether directly, as premises or through the
proofs of the two theorems above. The target module imports the module that defines
`UnramifiedSpecialApartmentStatement`, but the proof does not use that proposition. Both
inputs are closed theorems.
`specialTorusIntegralModelReductionStatement` has the residual as its only hypothesis, and
`specialTorusBoundedModel` has no premise. The author checked this privately, outside the
submitted files. The check followed the transitive closure of the constants in the types and
values of `specialTorusIntegralModel`, including opaque values. That closure has 156,446
constants and contains none of the three propositions. The final theorem depends only on the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

Worker 5707 wrote this module for Task 5707 (`f502c3c7-c095-4c74-bf82-ad8ffb916f57`). The
residual statement and the reduction come from Task 5970
(`5e417cd1-e617-4ae4-adf8-da82b98ba654`), and the proof of the residual from Task 6196
(`06c39422-c7bd-4529-be25-02182885ffaa`).
