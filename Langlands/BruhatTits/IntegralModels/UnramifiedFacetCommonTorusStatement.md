# Common maximal split tori and Lie-weight signs for descended facet models (KP Axiom 4.1.22(3))

This module states, as the unproved proposition
`UnramifiedFacetCommonTorusStatement`, part (3) of KP Axiom 4.1.22 for the
facet models over `𝒪[F]` obtained by unramified descent. For facets
`F ≺ F′`, the special fibre of the integral torus of `𝒢^0_{F′}` maps to a
maximal split torus of the special fibre of `𝒢^0_F` and of its maximal
reductive quotient `G_F`. The nonzero weights of that torus on the Lie
algebra of `℘_F(F′)` are the roots that are nonnegative in the direction from
`F` to `F′`. The maximality in the special fibre of `𝒢^0_{F′}` itself is a
hypothesis here (see "Omitted source assertions").

## Sources

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (KP below).
Locators are printed page / PDF page. The cited parts are:

- Axiom 4.1.20 (the models `𝒢^1_Ω`, `𝒢^0_Ω` and, in (3), their integral
  tori), p. 163 / p. 194, and Axiom 4.1.22, pp. 163–164 / pp. 194–195;
- §4.1.28, p. 166 / p. 197. For quasi-split groups it assigns the parts of
  Axiom 4.1.22 to Chapter 8: part (1) is Proposition 8.4.15, parts (2)–(5)
  are Theorem 8.4.19, part (6) is Theorem 8.4.10 and part (7) is
  Corollary 8.4.12;
- Theorem 8.4.19, pp. 308–310 / pp. 339–341, over `O`;
- §§9.2.4–9.2.5, Theorem 9.2.7 and Definition 9.2.8, pp. 327–329 /
  pp. 358–360. They give the building `B(G) = B(G_K)^Γ`, whose facets are the
  sets `F^Γ = F ∩ B(G)` for the `Γ`-facets `F` of `B(G_K)`. They give the
  models over `o` as the unique descents (Fact 2.10.16) of the models over
  `O`, the equality `G(K)^0_{F^Γ} = G(K)^0_F`, and the descended integral
  torus, whose special fibre is a maximal `f`-split torus;
- §9.3.2 and Proposition 9.3.3, pp. 331–332 / pp. 362–363;
- Proposition 9.4.23, p. 357 / p. 388, and Corollary 9.4.31, p. 361 /
  p. 392;
- §9.5, pp. 363–364 / pp. 394–395, which says how each part of
  Axiom 4.1.22 over `k` follows from the case over `K`;
- Lemma 2.10.9 and Corollaries 2.10.10 and 2.10.11, pp. 123–124 /
  pp. 154–155, and Definition 2.10.15 and Fact 2.10.16, p. 126 / p. 157;
- Lemma 2.6.24, p. 104 / p. 135, and Proposition 7.7.5(1), p. 269 / p. 300.

Here `k` has a Henselian discrete valuation, integers `o` and perfect residue
field `f`. `K` is a maximal unramified extension of `k`, with integers `O`,
and `Γ = Gal(K/k)`. The registered corrections
`kaletha-prasad-2024-corrections` (SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`) affect
the cited results in two ways (PDF pp. 37–38). They assume a perfect residue
field in §§8.3–8.4. They also insert the definition of `ρ_{Ω,Ω′}`, from the
inclusion `G(K)^0_{Ω′} ⊂ G(K)^0_Ω`, just before Proposition 8.4.15. Here the
residue field is finite, hence perfect. The Chapter 9 items of the
corrections (PDF pp. 39–42) do not touch the cited parts of Chapter 9. The
Library's KP source ledger (`notes/bruhat-tits/kp-source-ledger.md`) records
that the index set in Theorem 8.4.19(1) is false. That part is not used
here.

## Source assertion

Take facets `F ≺ F′` of `B(G)`. Let `S` be a maximal `k`-split torus whose
apartment contains `F′`, let `𝒮` be the closed `o`-split torus of `𝒢^0_{F′}`
with generic fibre `S`, and let `S̄` be its special fibre. Part (3) of Axiom
4.1.22 says two things. First, `S̄` is a maximal `f`-split torus of
`𝒢̄^0_F` as well as of `𝒢̄^0_{F′}`, and its isomorphic image in `G_F` is a
maximal `f`-split torus of `G_F`. Second, let `x ∈ F` and `v ∈ V(S)` with
`v + x ∈ F′`. Then the nonzero weights of `S̄` on the Lie algebra of
`℘_F(F′)` are the roots `a` of `G_F` (with respect to `S̄`) with
`a(v) ≥ 0`.

For the quasi-split group over `K`, §4.1.28 assigns this part to Theorem
8.4.19. The proof of 8.4.19(2) computes the roots of `S̄` in `p_F(F′)` as the
parabolic subset `Ψ_F(F′)`. Over `k`, §9.2.5 descends the `O`-torus of Axiom
4.1.20(3) to a closed `o`-torus of `𝒢^0_Ω`. If its generic fibre contains
a maximal `k`-split torus `S`, the special fibre of the maximal `o`-split
subtorus is a maximal `f`-split torus of `𝒢̄^0_Ω`. §9.5 says that (3) follows from the case over `K` through
the bijection between facets of `B` and `Γ`-invariant facets of `B(G_K)`,
using Corollary 9.4.31.

## Lean statement

All declarations are in namespace `Langlands.BruhatTits.IntegralModels`, at
the arbitrary universe `u`. The module has one auxiliary declaration, the
private instance `unramifiedFacetCommonTorusAffineHom`. It says that the base change of an affine
group scheme along `F → inertiaFixedField F` is affine, by pullback
stability, and it is needed to form `MaximalUnramified.BuildingData`. It is
private and adds nothing to the interface.

`UnramifiedFacetCommonTorusStatement.{u}` is an unproved, `Prop`-valued definition. The other four
statements of this family
(`UnramifiedFacet{ParabolicImage,ParabolicOrder,CommonTorus,RootDatum,PositiveRadical}Statement`)
share its first inputs:

- A nonarchimedean local field `F : Type u` (`Field`, `ValuativeRel`,
  `TopologicalSpace`, `IsNonarchimedeanLocalField`), of either
  characteristic, and a group scheme `G` over `Spec F` with
  `IsAffineHom G.X.hom`.
- `P : ParahoricBuildingData G`, a polysimplicial realization `R` and an
  apartment splitting `T` of `B = P.toValuationBuildingData`. They carry
  exactly the seven hypotheses of the published
  `Langlands.Geometry.Building.IntegralModelAxiomsStatement`:
  `SatisfiesBuildingAxiom R`, `HasBoundedOpenStabilizers`,
  `SatisfiesAffineApartmentAxiom T`, `HasRootReflections`,
  `SatisfiesApartmentAxioms`, `HasCompatibleApartmentFacets` and
  `HasTitsSystem`.
- `K = inertiaFixedField F`, the fixed field of inertia in the chosen
  separable closure. This is the maximal unramified extension. Its valuation
  ring `fixedFieldIntegers F` is KP's `O`, which is strictly Henselian.
  The other data are `C : MaximalUnramified.BuildingData F (baseChanged F K G)`
  (building data of `G_K`), `A : MaximalUnramified.SemilinearApartmentData C`
  (a semilinear `Gal(K/F)`-action `A.action` on the reduced building of `C`),
  a map `e` from the reduced building of `B` to that of `C`, and a real
  affine map `a : B.Apartment →ᵃ[ℝ] C.Apartment`. Their hypotheses are
  exactly the eight conclusions of
  `Langlands.Geometry.Building.UnramifiedApartmentDescentStatement` (Task
  5877, `94d9a827-c647-49dc-97ed-13e24b678db8`, revision 3), with `B.S`,
  `B.i` written as `P.S`, `P.i`. That statement is not yet in the Library,
  so they are spelled out:
  1. `e` is injective;
  2. `e (g • z) = rationalExtend F K G g • e z` for every `g ∈ G(F)`;
  3. `e (B.apartmentMap w) = C.apartmentMap (a w)` for every apartment point
     `w`;
  4. every `A.action σ` fixes every point `e z`;
  5. every point fixed by all `A.action σ` is some `e z`;
  6. if `e z` is a special point of `C`, then `z` is a special point of `B`;
  7. `a ⁻¹' facet C.affineRoots (a w) = facet B.affineRoots w` for every
     `w`;
  8. every `s` in the `characterValuationKernel` of `P.S` over `K` (for
     `MaximalUnramified.valuation F`), mapped to `G(K)` by the base change
     of `P.i`, fixes `e (B.apartmentMap w)` for every `w`.
- `E : UnramifiedZeroDatum F (baseChanged F K G)`. Its `E.zeroPoints` is the
  published `G(K)^0` (KP Definition 2.6.23(1)).

In this file, a pair `D : RelativeComponentModelData ↥𝒪[F] F G` (a full
model and its relative component over `𝒪[F]`) is *characterized for a facet
`Fc : BuildingFacet B`* when

```lean
D.neutral.IsSmooth ∧
  D.neutral.baseChangeUnramified.integralPoints =
    E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)
```

The Lean statement writes out both conditions at each use, so "characterized"
is only a word of this file. The full model of `D` is not constrained.

The inputs specific to this statement are:

- facets `Fc Fc′` of `B`, a rational point `g` of `G` and apartment subsets
  `Fa Fa′` of `B` with `AffineRootSystem.IsFaceOf B.affineRoots Fa Fa′`,
  `Fc.val = B.translatedApartmentMap g '' Fa` and
  `Fc′.val = B.translatedApartmentMap g '' Fa′`. So `Fc ≺ Fc′`, presented
  in the translated apartment `g • A(S)`, which is the apartment of
  `gSg⁻¹`;
- pairs `D` and `D′` characterized for `Fc` and `Fc′`;
- any published model morphism `φ : RelativeComponentModelHom D′ D`;
- `Q : SpecialFibreQuotientData D` with `Q.IsReductiveQuotient`, so that
  `Q.quotient` is the source's `G_F`;
- `𝒯 : IntegralTorusData D′ B.S (B.i ≫ (G.innerIso g).hom)` with
  `𝒯.SatisfiesTorusClause`. This is a closed split torus of `D′.neutral`
  (`IsClosedSplit`) whose generic fibre is `S` with inclusion `Int(g) ∘ i`,
  and whose special fibre is a maximal split torus of the special fibre of
  `D′.neutral` (`HasMaximalSplitSpecialFibre`). The closed split torus with
  a given generic fibre is unique, so this is the source's `𝒮` for the torus
  `gSg⁻¹`, as in Axiom 4.1.20(3).

The conclusion has three parts:

- `IsMaximalSplitTorus (φ.targetTorusInclusion 𝒯)`: the special fibre of
  `𝒯`, mapped by the special fibre of `φ.neutral`, is a maximal split torus
  of the special fibre of `D.neutral`;
- `IsMaximalSplitTorus (φ.quotientTorusInclusion Q 𝒯)`: further projected
  to `Q.quotient`, it is a maximal split torus there;
- for every proof `hT` that `𝒯` is split,
  `φ.HasApartmentLieWeightSignFormula B Q 𝒯 hT Fa Fa′`. Take `x ∈ Fa` and
  `v` in the real cocharacter space of `S` whose class carries `x` into
  `Fa′`. The nonzero weights of the torus on the Lie algebra of the image of
  `D′` in `Q.quotient` (`nonzeroLieImageWeights`) are then exactly the
  relative roots `χ` of `Q.quotient` for this torus whose generic character,
  transported through `𝒯`, is nonnegative on `v`.

## Why these hypotheses state the source's assertion

**The groups.** `C` is building data of `G_K` in the sense of KP
Chapters 6–7: a supplied apartment class with its reduced building, root
filtrations and fixers. `A` is a semilinear Galois action on it. By
hypotheses 1, 4 and 5, `e` is a bijection from the reduced building of `B`
onto the points fixed by every `A.action σ`. By hypotheses 2, 3 and 7 it is
compatible with `G(F)`, with the apartments and with their affine-root
facets. Hypotheses 6 and 8 carry over special points and the action of the
bounded part of the torus. These are the properties of KP's inclusion
`B(G) = B(G_K)^Γ ⊂ B(G_K)` (Theorem 9.2.7, Definition 9.2.8) that are used
here. Corollary 9.4.31 says that the facets of §9.2.4 are the facets cut
out by affine root hyperplanes. Through `e`, a facet `Fc` of `B` is
therefore `F^Γ` for the unique `Γ`-facet `F` of `B(G_K)` that contains
`e '' Fc.val`. By KP Lemma 2.6.24, `E.zeroPoints = G(K)^0` does not depend
on the torus used to compute it. The Library states this independence as
`Langlands.Geometry.Building.UnramifiedZeroIndependenceStatement`. So the
right-hand side `E.zeroPoints ⊓ C.pointwiseFixer (e '' Fc.val)` is the
pointwise fixer of `F^Γ` in `G(K)^0`. This is `G(K)^0_{F^Γ}` by
Proposition 7.7.5(1) over `K`, and it equals `G(K)^0_F` by §9.2.5. Hence
also `𝒢^0_{F^Γ} = 𝒢^0_F`, and below `F` stands for either facet. The
statement quantifies over every `C`, `A`, `e`, `a` and `E` with these
properties instead of fixing one construction. The source's argument
(§9.5) is the same for each choice.

**The models.** KP define `𝒢^0_F` over `o` in §9.2.5 as the descent
(Fact 2.10.16) of the smooth affine `O`-model with `O`-points `G(K)^0_F`.
So `𝒢^0_F` is a smooth integral model of `G` over `o` with
`𝒢^0_F(O) = G(K)^0_F`. A Library `IntegralModel` is affine, flat and of
finite type with a chosen generic-fibre identification, which is KP's
"integral model" (§2.10). For a characterized pair `D`, the integral points
of `D.neutral.baseChangeUnramified` are the `O`-points `D.neutral(O)`
inside `G(K)`, and they equal `G(K)^0_F`. Lemma 2.10.9 recovers the
coordinate ring of a smooth integral model `X` over `o` from these points as
`o[X] = {f ∈ k[X] | f(X(O)) ⊂ O}`. Corollary 2.10.11 says that
`X ↦ X(O) ⊂ X(K)` is fully faithful on smooth integral models. So
`D.neutral` and `𝒢^0_F` are isomorphic by a unique isomorphism that is the
identity on generic fibres. Conversely, `𝒢^0_F` with its generic
identification satisfies both conditions. For model morphisms, Corollary
2.10.10 shows that a morphism extending the identity of `G` exists from the
model for `F′` to the model for `F` when `G(K)^0_{F′} ⊂ G(K)^0_F`, and that
it is unique. Uniqueness is also the published
`Langlands.GroupScheme.IntegralModel.Hom.hom_eq`. So the neutral part of any
`RelativeComponentModelHom` between characterized pairs is the source's
`ρ_{F,F′}` (§9.3.2) under these isomorphisms. The conclusions are built from
the neutral models, their special fibres, schematic images, residue-field
points and integral sections, and the given quotients and tori. These are
carried along isomorphisms of models that are the identity on generic
fibres. Hence, for characterized models, the conclusion is the source's
assertion for `𝒢^0_F` and `ρ_{F,F′}`. Quantifying over all characterized
models and all model morphisms adds no case beyond the source's objects. It
needs no uniqueness or chosen-model premise, and a consumer may apply the
statement to models built in any way.

**Why not `𝒪[F]`-points.** The residue field of `𝒪[F]` is finite. Lemma
2.10.9 and Corollary 2.10.11 need the points over the strictly Henselian
ring `O`. Axiom 4.1.20 itself notes that the condition
`𝒢^1_Ω(o) = G(k)^1_Ω` determines the model when `k` is strictly Henselian
(Corollary 2.10.11). Over `𝒪[F]`, the `𝒪[F]`-points do not determine a
smooth model. This holds even among models with connected fibres, as
`RelativeComponentModelData` requires of its neutral model
(`neutral_connectedFibres`). For example, let the residue field be `𝔽_2`
(as for `F = ℚ_2` or `𝔽_2((t))`), let `π` be a uniformizer, and let
`G = 𝔾_m`. The dilatation of `𝔾_{m,𝒪[F]}` along its identity section is
`Spec 𝒪[F][y, (1 + πy)^{-1}]`, with coordinate `x = 1 + πy` and group law
`y ⊙ y′ = y + y′ + πyy′`. It is a smooth affine group model of `𝔾_m`. Its
special fibre is `𝔾_a`, which is connected. Its `𝒪[F]`-points are
`1 + π𝒪[F]`, and this is all of `𝒪[F]^× = 𝔾_m(𝒪[F])` because `𝔽_2^×` is
trivial. Its `O`-points `1 + πO` form a proper subgroup of `O^×`, however,
and it is not isomorphic to `𝔾_{m,𝒪[F]}`, whose special fibre is `𝔾_m`.
Here `G(K)^0 = O^×`, and the source's model for the unique facet is
`𝒢^0_F = 𝔾_{m,𝒪[F]}`, with `𝒢^0_F(𝒪[F]) = 𝒪[F]^×`. So smoothness,
connected fibres and a condition `D.neutral.integralPoints = G(F)^0_F`
would admit the dilatation as well, a model about which the source asserts
nothing. KP's own characterization uses the `O`-points, in Axiom 4.1.20,
in §9.2.5 and in Definition 2.10.15. Definition 2.10.15 realizes a subset
`U ⊂ X(K)` by the necessarily unique smooth model over `o` with
`O`-points `U`. The statements follow that characterization.

**The hypotheses on `P`.** The seven hypotheses are those of the consumer's
target `IntegralModelAxiomsStatement`. Every consumer has them, and a prover
may use them.

## Further remarks

- **Translated charts.** The source uses the apartment of any maximal split
  torus containing `F′`. Every apartment of `B` is a translated apartment
  `g • A(S)`. The published formula is written in the coordinates of `A(S)`,
  with the torus included by `Int(g) ∘ i`.
- **Any `φ`.** The source's `ρ_{F,F′}` is the unique model morphism with
  identity generic fibre (rigidity above).
- **The proof `hT`.** Splitting of `𝒯` is part of the hypothesis
  `IsClosedSplit`. The formula is asserted for every proof of it, as in the
  `lie_weight_signs` field.

## Omitted source assertions

Across the five statements, two assertions of KP Axiom 4.1.22 are not
concluded:

- **Reduction surjectivity in (7).** KP call `π_F : 𝒢^0_F(o) → 𝒢^0_F(f)`
  surjective. The Library clause `SatisfiesPositiveRadicalClause` asserts
  that both reduction maps are surjective.
  `UnramifiedFacetPositiveRadicalStatement` concludes only the inclusion.
  Surjectivity follows from smoothness over the Henselian ring `𝒪[F]` by
  the published `Langlands.GroupScheme.IntegralModel.reduction_surjective`,
  and the consumer proves it.
- **Maximality in the larger facet's model in (3).** KP say that `S̄` is a
  maximal `f`-split torus of the special fibre of `𝒢^0_{F′}`. In
  `UnramifiedFacetCommonTorusStatement` this is part of the hypothesis
  `𝒯.SatisfiesTorusClause` (its `HasMaximalSplitSpecialFibre` conjunct, with
  `IsClosedSplit`), which the consumer has from Axiom 4.1.20(3). So it is not
  concluded again.

Three things in the consumer's target are not stated here. The first is
the preamble and part (1) of Axiom 4.1.22, for all bounded subsets (the
Library's `SatisfiesGeneralMorphismAxioms`). The second is the
`reductive_quotients` field of `FacetAxiomClauses`. The third is the
reduction surjectivity above. The consumer proves them separately.

For this statement, the maximality of `S̄` in the special fibre of
`𝒢^0_{F′}` is a hypothesis and not a conclusion, as described above.
Everything else in part (3) is concluded.

## Intended consumer

The consumer is the construction of the integral models for KP Axioms 4.1.20
and 4.1.22 in Task 5429 (`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`), whose final
target is `IntegralModelAxiomsStatement`. Its facet models are
relative-component pairs over `𝒪[F]`, obtained by unramified descent of the
parahoric models over `fixedFieldIntegers F`. Their neutral models are smooth
with exactly the unramified integral points above, and their integral tori
satisfy `SatisfiesTorusClause`. It applies this statement to the
fields `common_tori` and `lie_weight_signs` of
`BuildingModelQuotientFamily.FacetAxiomClauses`. The conjuncts
`T.IsClosedSplit` and `T.HasMaximalSplitSpecialFibre` of those fields come
from the consumer's torus hypothesis.
