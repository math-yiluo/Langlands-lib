# The root datum of the reductive quotient of a descended facet model (KP Axiom 4.1.22(6))

This module states, as the unproved proposition
`UnramifiedFacetRootDatumStatement`, part (6) of KP Axiom 4.1.22 for the
facet models over `𝒪[F]` obtained by unramified descent. The root datum of the
maximal reductive quotient `G_F`, with respect to the special fibre of the
integral torus, consists of the derivatives of the affine roots vanishing on
`F` and their coroots.

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
- Theorem 8.4.10(2), p. 305 / p. 336, over `O`, and the coroots of
  §2.6.4;
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

Part (6) of Axiom 4.1.22 says that the root datum of `G_F` with respect to
the maximal `f`-split torus `S̄` is `(X^*(S̄), Φ_F, X_*(S̄), Φ_F^∨)`. Here
`Φ_F ⊂ Φ ⊂ X^*(S)` is the image, under the derivative map `Ψ → Φ`, of the
set `Ψ_F` of affine roots that vanish on `F`, and
`Φ_F^∨ = {a^∨ ∈ Φ^∨ | a ∈ Φ_F}`. The lattices of `S̄` are identified with
those of `S` through the integral torus.

For the quasi-split group over `K`, §4.1.28 assigns this part to Theorem
8.4.10, whose part (2) is this root datum over `O`. Over `k`, §9.5 says that
(6) was proved in Proposition 9.4.23. That proposition gives the relative
root datum of `G_Ω` with respect to `S̄` as `(X^*(S̄), Φ_Ω, X_*(S̄), Φ_Ω^∨)`
for a nonempty bounded subset `Ω` of an apartment of `B`.

## Lean statement

All declarations are in namespace `Langlands.BruhatTits.IntegralModels`, at
the arbitrary universe `u`. The module has one auxiliary declaration, the
private instance `unramifiedFacetRootDatumAffineHom`. It says that the base change of an affine
group scheme along `F → inertiaFixedField F` is affine, by pullback
stability, and it is needed to form `MaximalUnramified.BuildingData`. It is
private and adds nothing to the interface.

`UnramifiedFacetRootDatumStatement.{u}` is an unproved, `Prop`-valued definition. The other four
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

- a facet `Fc` of `B`, a rational point `g` of `G` and an apartment subset
  `Fa` with `AffineRootSystem.IsFacet B.affineRoots Fa` and
  `Fc.val = B.translatedApartmentMap g '' Fa`;
- a pair `D` characterized for `Fc`;
- `Q : SpecialFibreQuotientData D` with `Q.IsReductiveQuotient`, so that
  `Q.quotient` is the source's `G_F`;
- `𝒯 : IntegralTorusData D B.S (B.i ≫ (G.innerIso g).hom)` with
  `𝒯.SatisfiesTorusClause`, the torus of Axiom 4.1.20(3) for `gSg⁻¹`;
- any `Droot : RelativeRootReflectionData B.i`. It gives a coroot and a
  normalizer representative for every relative root, and the representative
  acts on characters by the reflection with that coroot.

The conclusion is `HasApartmentDerivativeRootDatum B Q 𝒯 Droot hT Fa`, for
every proof `hT` that `𝒯` is split. It asserts a finite-indexed root datum
that is the root datum (`IsRootDatumOf`) of `Q.quotient` with respect to the
special fibre of `𝒯` mapped into it. Its root-coroot pairs are exactly the
pairs `(a, Droot.coroot a)`, for `a` a relative root that is the derivative
of an affine root of `B` vanishing on `Fa` (`facetDerivativeRoots`), both
transported to the special torus through `𝒯`.

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
smooth model. Let `π` be a uniformizer and
`q` the order of the residue field. The dilatation
`𝒪[F][x, (x^q − x)/π]` of `𝔾_a` along the finite subgroup `𝔽_q` of its
special fibre is a smooth affine group model of `𝔾_a`. Every element of
`𝒪[F]` reduces into `𝔽_q`, so this model has the same `𝒪[F]`-points as
`𝔾_{a,𝒪[F]}`. But its special fibre has `q` components, and its `O`-points
differ from `O`. The same dilatation, along the finite subgroup of
residue-field points of the special fibre, works for every
positive-dimensional `𝒢^0_F`. A condition `D.neutral.integralPoints = G(F)^0_F` would
therefore admit models other than `𝒢^0_F`, about which the source asserts
nothing. KP's own characterization uses the `O`-points, in Axiom 4.1.20,
in §9.2.5 and in Definition 2.10.15. Definition 2.10.15 realizes a subset
`U ⊂ X(K)` by the necessarily unique smooth model over `o` with
`O`-points `U`. The statements follow that characterization.

**The hypotheses on `P`.** The seven hypotheses are those of the consumer's
target `IntegralModelAxiomsStatement`. Every consumer has them, and a prover
may use them.

## Further remarks

- **Every `Droot`.** The coroots of any `RelativeRootReflectionData` are the
  source's `a^∨`. The representative of `a` gives an element `w` of the
  finite relative Weyl group that acts on `X^*(S) ⊗ ℚ` by
  `χ ↦ χ − ⟨χ, c⟩a`, with `⟨a, c⟩ = 2`. This is a reflection sending `a` to
  `−a`. For a `W`-invariant inner product, an element of `W` is orthogonal,
  so its fixed hyperplane `ker c` is the orthogonal complement `a^⊥` of its
  `−1`-eigenvector. Hence `c = 2(a, ·)/(a, a) = a^∨`. Quantifying over every
  `Droot` therefore states the source's coroots. The existence of some
  `Droot` is the published statement
  `Langlands.GroupScheme.RelativeRootReflectionExistenceStatement`, which is
  not used here.
- **Translated charts.** As for the Lie-weight formula, every apartment is a
  translated apartment `g • A(S)`. The derivative roots are computed in the
  coordinates of `A(S)`, and the torus is included by `Int(g) ∘ i`.
- **Relative root datum.** `IsRootDatumOf` asks three things: the pairing is
  the lattice pairing, the roots are the roots of the special torus in
  `Q.quotient`, and each reflection is induced by a residue-field point
  normalizing that torus. For the maximal split torus this is the relative
  root datum of Proposition 9.4.23.

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

For this statement the two omissions above do not arise. Part (6) is stated
for every facet presentation, as in the `derivative_root_data` field.

## Intended consumer

The consumer is the construction of the integral models for KP Axioms 4.1.20
and 4.1.22 in Task 5429 (`cd2ad671-3edf-4905-a0e2-e7aa2b160b91`), whose final
target is `IntegralModelAxiomsStatement`. Its facet models are
relative-component pairs over `𝒪[F]`, obtained by unramified descent of the
parahoric models over `fixedFieldIntegers F`. Their neutral models are smooth
with exactly the unramified integral points above, and their integral tori
satisfy `SatisfiesTorusClause`. It applies this statement to the
field `derivative_root_data` of `BuildingModelQuotientFamily.FacetAxiomClauses`.
