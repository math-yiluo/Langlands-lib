# The Lie-weight sign formula over the maximal unramified extension (KP Theorem 8.4.19(2))

This module states, as the unproved proposition
`UnramifiedFacetLieWeightSignStatement`, the second part of KP Theorem 8.4.19 for
the connected reductive group `G` over `K`, the maximal unramified extension of a
nonarchimedean local field `F`. Take incident facets `Ωf ≺ Ωf′` of the apartment
of a maximal `K`-split torus `S`. Take the smooth zero-fixer models over the
integers `O` of `K` for (subsets of) these facets, and the model morphism between
them. The nonzero weights of the special fibre of the integral torus of `S` on the
Lie algebra of the image of the larger facet's model in the reductive quotient of
the smaller facet's model are then the roots that are nonnegative in the direction
from `Ωf` to `Ωf′`.

It is the input over `O` for the descent of §9.5 that proves the sign part of the
published `UnramifiedFacetCommonTorusStatement` (KP Axiom 4.1.22(3) over `F`).

## Sources

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (KP below).
Locators are printed page / PDF page.

- Theorem 8.4.19, pp. 308–310 / pp. 339–341, part (2) and its proof;
- Axiom 4.1.20(3), p. 163 / p. 194, and Axiom 4.1.22(3), pp. 163–164 /
  pp. 194–195, the form in which the result is used;
- §4.1.28, p. 166 / p. 197, which assigns Axiom 4.1.22(3) for quasi-split groups
  to Theorem 8.4.19;
- Lemma 2.10.9 and Corollaries 2.10.10 and 2.10.11, pp. 123–124 / pp. 154–155,
  and Definition 2.10.15, p. 126 / p. 157 (smooth models over a strictly
  Henselian ring are determined by their integral points);
- Lemma 2.6.24, p. 104 / p. 135, and Proposition 7.7.5(1), p. 269 / p. 300
  (`G(K)^0` and the fixers `G(K)^0_Ω`).

The registered corrections `kaletha-prasad-2024-corrections` (SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF
pp. 37–38) assume a perfect residue field in §§8.3–8.4 and insert the definition
of `ρ_{Ω,Ω′}` before Proposition 8.4.15. The residue field of `O` is an algebraic
closure of the finite residue field of `F`, so it is perfect. The Library's KP
source ledger (`notes/bruhat-tits/kp-source-ledger.md`) records that the index
set in Theorem 8.4.19(1) is false; part (1) is not used here.

## Source assertion

In Chapter 8, `G` is quasi-split over a field with a strictly Henselian discrete
valuation and perfect residue field, `S` is a maximal split torus and `A(S)` its
apartment. For facets `F ≺ F′` of `A(S)`, `𝒢^0_F` and `𝒢^0_{F′}` are the
smooth affine models with `O`-points `G(K)^0_F` and `G(K)^0_{F′}`,
`ρ_{F,F′} : 𝒢^0_{F′} → 𝒢^0_F` is the model morphism extending the identity,
`G_F` is the maximal reductive quotient of the special fibre of `𝒢^0_F`, and
`℘_F(F′)` is the image of the special fibre of `𝒢^0_{F′}` in `G_F`. The
closed `O`-torus `𝒮` of `𝒢^0_{F′}` with generic fibre `S` has special fibre
`S̄`. Theorem 8.4.19(2) says: for `x ∈ F` and `v ∈ V(S)` with `x + v ∈ F′`, the
nonzero weights of `S̄` on `Lie(℘_F(F′))` are the roots `a` of `G_F` with
respect to `S̄` with `a(v) ≥ 0`, where characters of `S̄` are identified with
characters of `S` through `𝒮`.

## Lean statement

All declarations are in namespace `Langlands.BruhatTits.IntegralModels`, at the
arbitrary universe `u`. Three private instances say that the neutral special
fibre of a relative-component model pair is affine over its base and as a scheme,
and that the supplied quotient is affine. They are needed to form
`nonzeroLieImageWeights` and `relativeRoots`, and they add nothing to the
interface.

`UnramifiedFacetLieWeightSignStatement.{u}` is a `Prop`-valued definition. Its
inputs are:

- a nonarchimedean local field `F : Type u` (`Field`, `ValuativeRel`,
  `TopologicalSpace`, `IsNonarchimedeanLocalField`);
- a group scheme `G` over `K = inertiaFixedField F` with `IsAffineHom G.X.hom`.
  `K` is the maximal unramified extension and `O = fixedFieldIntegers F` its
  valuation ring, which is strictly Henselian;
- `C : MaximalUnramified.BuildingData F G`, the published KP building data of `G`
  over `K` (for the valuation `MaximalUnramified.valuation F`). It includes that
  `G` is connected reductive and a maximal split torus `C.i : C.S → G`, and its
  apartment `C.Apartment` is `A(C.S)`, with `C.affineRoots`,
  `C.apartmentMap : C.Apartment → C.ReducedBuilding` and pointwise fixers
  `C.pointwiseFixer`;
- `E : UnramifiedZeroDatum F G`; `E.zeroPoints` is `G(K)^0` (KP Definition
  2.6.23(1));
- apartment subsets `Ωf Ωf′ Ω Ω′` with
  `AffineRootSystem.IsFaceOf C.affineRoots Ωf Ωf′` (so `Ωf` and `Ωf′` are facets
  and `Ωf ≺ Ωf′`), `Ω ⊆ Ωf` and `Ω′ ⊆ Ωf′`;
- relative-component model pairs `D D′` over `O` with generic fibre `G`, whose
  neutral models are smooth (`IsSmooth`) and satisfy

  ```lean
  D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)
  D'.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')
  ```

- any model morphism `φ : RelativeComponentModelHom D′ D`;
- `Q : SpecialFibreQuotientData D` with `Q.IsReductiveQuotient`;
- `A : IntegralTorusData D′ C.S C.i` with `hA : IsSplitTorus A.torus.toGrp`: a
  split `O`-torus mapping to the neutral model of `D′`, whose generic fibre is
  identified with `C.S` compatibly with `C.i`.

The conclusion: for every `x ∈ Ω` and every `v : RealTorusSpace.V C.S` with
`(Submodule.Quotient.mk v : TranslationSpace C.i) +ᵥ x ∈ Ω′`,

```lean
nonzeroLieImageWeights (φ.quotientTorusInclusion Q A) (φ.reductiveImageInclusion Q) =
  {χ | χ ∈ relativeRoots (φ.quotientTorusInclusion Q A) ∧
    0 ≤ RealTorusSpace.eval C.S ((A.characterSpecialization hA).symm χ) v}
```

Here `φ.quotientTorusInclusion Q A` is the special fibre of `A`, mapped by the
special fibre of `φ.neutral` and then by `Q.projection`, and
`φ.reductiveImageInclusion Q` is the schematic image of the special fibre of
`D′.neutral` in `Q.quotient`. The left side is the set of nonzero characters
whose weight space in `Lie(Q.quotient)` meets the image of `Lie` of that
schematic image. The right side consists of the roots of `Q.quotient` for the
torus whose generic character, through `A.characterSpecialization hA`, is
nonnegative on `v`. This is exactly the published
`RelativeComponentModelHom.HasLieWeightSignFormula`, written out because that
definition requires `[IsNonarchimedeanLocalField K]` and a
`ValuationBuildingData`, while `K` here is the maximal unramified extension and `C`
is integer-valuation building data.

## Why the statement is the source's assertion

**The models.** `O` is strictly Henselian. By Lemma 2.10.9 and Corollary
2.10.11 a smooth integral model over `O` is determined, up to unique isomorphism
that is the identity on generic fibres, by its `O`-points in `G(K)`, and by
Corollary 2.10.10 a model morphism extending the identity is unique. The
published `Langlands.GroupScheme.IntegralModel.Hom.hom_eq` is that uniqueness.
By Lemma 2.6.24 `E.zeroPoints = G(K)^0` does not depend on the torus used to
compute it, and `G(K)^0 ∩ G(K)_{F}` is `G(K)^0_F` (Proposition 7.7.5(1)). So for
nonempty `Ω` the neutral model of `D` is `𝒢^0_{Ω}`, and `φ.neutral` is
`ρ_{Ω,Ω′}`. The conclusion is built from the neutral models, their special fibres,
the schematic image, the supplied quotient and the supplied torus, all of which
are carried along isomorphisms of models that are the identity on generic fibres.

**Subsets of facets.** For `x ∈ Ωf` the fixer `G(K)^0_x` equals `G(K)^0_{Ωf}`
(the affine roots nonnegative at `x` are those nonnegative on its facet), so for
nonempty `Ω ⊆ Ωf` the model is the source's `𝒢^0_{Ωf}`, and similarly for `Ω′`.
If `Ω` or `Ω′` is empty, the conclusion is vacuous. The conclusion for
`x ∈ Ω`, `v + x ∈ Ω′` is the source's assertion for those points of `Ωf`, `Ωf′`.
Allowing subsets is what the descent can supply: a descended facet `Fa` of the
apartment over `F` maps by `a` into a facet of `A(C.S)`, but the Library does
not state that its image is the whole facet.

**The torus and characters.** A split `O`-torus with generic fibre `C.S` and a
compatible map to the neutral model of `D′` is unique up to unique isomorphism
(homomorphisms between flat separated models are determined on generic fibres,
and split tori over the normal domain `O` have the same characters as their
generic fibres). So `A` is the source's `𝒮`; its closedness in the model is not
needed to state the formula. `A.characterSpecialization hA` is the source's
identification of characters of `S̄` with characters of `S` through `𝒮`. The
formula is asserted for every proof `hA`, as in the published sign clause.

**The quotient.** `Q.IsReductiveQuotient` says that `Q.radicalInclusion` is the
unipotent radical of the neutral special fibre, `Q.projection` is its represented
fppf quotient and `Q.quotient` is connected reductive. So `Q.quotient` is
`G_{Ωf}`, and the schematic image is `℘_{Ωf}(Ωf′)`.

**Vectors.** The source's `v ∈ V(S)` acts on the apartment through its class in
`TranslationSpace C.i = V(S)/V(S)^Φ`, which is the expression `x + v` here.

## Intended consumer

Task 6320 (`0d9f960a-6d9d-4ba2-bc9b-3c0a847189c2`) proves the published
`UnramifiedFacetCommonTorusStatement`. Its sign part, for models over `𝒪[F]`
characterized by their points after base change to `O`, is deduced from this
statement as in KP §9.5: base change `D`, `D′`, `φ` and `Q` to `O` and to the
residue field of `O`, transport the translated apartment `g • A(S)` back to `A(S)`
by `Int(g)⁻¹`, and restrict weights from the maximal `K`-split torus `C.S` to the
base change of the maximal `F`-split torus.
