# Source descent of étaleness in the localized analytic category

This module contains only the Prop-valued definition
`Langlands.Analytic.SaturatedAtlasPresentation.LocalizedEtaleSourceDescentStatement`:
a morphism of analytic spaces is étale if its composites with a family of étale
maps to its source that is jointly surjective on points are étale. The file
states the proposition and does not prove it.

## Exact statement

`LocalizedEtaleSourceDescentStatement.{u, v, w} : Prop` asserts: for every
field `K : Type u` with `NormedField K`, `IsUltrametricDist K` and
`CompleteSpace K`, every morphism `F : X ⟶ Y` of
`LocalizedCategory.{u, v, v} (K := K)`, every index type `ι : Type w` and every
family of morphisms `q i : U i ⟶ X` of the same category, if
1. every `q i` is étale (`etale (q i)`),
2. the `q i` are jointly surjective on underlying points: every
   `x : localizedSpaceFunctor.obj X` lies in the range of
   `localizedSpaceFunctor.map (q i)` for some `i`, and
3. every composite `q i ≫ F` is étale,

then `F` is étale.

- `etale` is the Library's localized étale predicate (module
  `Langlands.Geometry.Analytic.EtaleSite`): arrows isomorphic to the image of a
  strong map between constructed saturations that is étale over all affinoid
  pieces at every point (`StrongHom.IsEtaleAllPieces`).
- The field may carry the trivial norm: only `NormedField K` is assumed, the
  hypotheses under which the Library defines `LocalizedCategory` and `etale`.
- The universes of the field (`u`), of the analytic spaces (`v`) and of the
  index type (`w`) are independent.
- No Hausdorffness, goodness or strictness hypothesis is made on `X`, `Y` or the
  `U i`.

## Original sources

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`
(printed page = PDF page + 3):
- §1.2, printed p.14 (PDF p.11): the valuation of the ground field may be
  trivial throughout the paper.
- §3.2, printed pp.58–59 (PDF pp.55–56): Proposition 3.2.1 (a finite morphism
  of `k`-affinoid spaces `M(𝓑) → M(𝒜)` is flat at `y` if and only if the
  localization of `𝓑` at the prime of `y` is flat over the localization of `𝒜`
  at the prime of its image), Proposition 3.2.3 (for a finite morphism,
  flatness at `y` over finitely many affinoid domains covering a neighbourhood
  of the image point gives flatness over every affinoid domain containing it),
  Definition 3.2.5 (flatness of a quasifinite morphism at a point, through
  finite open models), Corollary 3.2.6 (flat quasifinite morphisms are
  preserved under composition and base change) and Proposition 3.2.7 (flat
  quasifinite morphisms are open maps).
- §3.3, printed pp.61–63 (PDF pp.58–60): Proposition 3.3.2(i) (for morphisms
  `Y → X → S`, the right-exact sequence
  `φ*(Ω_{X/S}) → Ω_{Y/S} → Ω_{Y/X} → 0`), Proposition 3.3.3(i)
  (`Ω_{Y'/X'} = f'*(Ω_{Y/X})` for the base change `Y' = Y ×_X X' → X'`),
  Definition 3.3.4 (a quasifinite morphism is unramified if `Ω_{Y/X} = 0` and
  étale if it is unramified and flat), the proof of Lemma 3.3.5 (for a finite
  morphism of `k`-affinoid spaces `M(𝓑) → M(𝒜)` the completed and the ordinary
  tensor products `𝓑 ⊗_𝒜 𝓑` agree, so `Ω_{Y/X}` is given by the algebraic
  module of differentials `Ω_{𝓑/𝒜}`), Corollary 3.3.8 (unramified and étale
  morphisms are preserved under composition and base change) and Corollary
  3.3.9 (if `ψ : Z → Y` and `φ : Y → X` are quasifinite, `φ ∘ ψ` is étale and
  `φ` is unramified, then `ψ` is étale: a cancellation property under these
  hypotheses).
- Definition 3.1.1, printed p.54 (PDF p.51): a morphism is finite at a point
  if it induces a finite morphism between open neighbourhoods, and
  quasifinite if it is finite at every point; quasifinite morphisms are
  locally separated and closed, so their relative boundary is empty
  (Definition 1.5.4, printed p.34).
- Corollary 3.1.10, printed p.57 (PDF p.54): a morphism is finite at `y` if and
  only if `y` is isolated in its fibre and lies in the relative interior.
- Proposition 1.5.5(ii), printed pp.34–35 (PDF pp.31–32): for morphisms
  `ψ : Z → Y` and `φ : Y → X`, the inclusion
  `Int(Z/Y) ∩ ψ⁻¹(Int(Y/X)) ⊆ Int(Z/X)` holds in general, and the equality
  `Int(Z/X) = Int(Z/Y) ∩ ψ⁻¹(Int(Y/X))` is stated under the sufficient
  hypotheses that `φ` is locally separated and good.
- §4.1, printed p.82 (PDF p.79): étale coverings are families of étale
  morphisms with jointly surjective images.

Conrad and Temkin, *Descent for nonarchimedean analytic spaces*, Tunisian
J. Math. 3 (2021), registered as `conrad-temkin-2021-descent-nonarchimedean`,
SHA256 `c39ae767f651247db138344cf2b52ea66a3b1e40e0c349aa3bbddb81aacc2d11`
(printed page = PDF page + 688): Lemma 2.9, printed pp.700–701 (PDF
pp.12–13). For morphisms `ψ : Z → Y` and `φ : Y → X` of `k`-analytic spaces,
`Int(Z/Y) ∩ ψ⁻¹(Int(Y/X)) ⊆ Int(Z/X)`, and a point of `Int(Z/X)` lies in
`Int(Z/Y) ∩ ψ⁻¹(Int(Y/X))` if it lies in `Int(Z/Y)` or if `φ` is separated on
an open neighbourhood of its image. No hypothesis on `φ` is needed in the
first case.

Temkin, *On local properties of non-Archimedean analytic spaces II*, Israel
J. Math. 140 (2004), author PDF registered as
`temkin-2004-local-properties-ii`, SHA256
`de9b630dccdaf8678a6ee43439de0d1b719e3bb2fb8cdebd02e6ca579b63ee90`:
Corollary 5.7, author PDF p.23, the equality
`Int(Z/X) = Int(Z/Y) ∩ ψ⁻¹(Int(Y/X))` whenever `φ` is locally separated, the
separated case of the lemma above.

Berkovich, *Spectral theory and analytic geometry over non-Archimedean fields*
(1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`:
- §2.1, printed pp.24–25 (PDF pp.38–39): a Banach module over a `k`-affinoid
  algebra `𝒜` is a finite Banach module if some finite free `𝒜`-module maps
  onto it by an admissible epimorphism, and a Banach `𝒜`-algebra is finite if
  it is a finite Banach `𝒜`-module. The example after Proposition 2.1.9 shows
  that, for a trivially valued field, a Banach module that is finite as an
  `𝒜`-module need not be a finite Banach module.
- Proposition 3.1.3(ii), printed p.49 (PDF p.63): the equality of relative
  interiors above for the analytic spaces of that book, which Berkovich 1993,
  §1.5 identifies with the good analytic spaces.

## Why the statement is expected to hold

Étaleness of a quasifinite morphism combines finiteness near each point,
flatness and unramifiedness (Definitions 3.1.1, 3.2.5 and 3.3.4). Fix a point
`x` of `X` and choose `i` and `u` with `q i (u) = x`.

**Finiteness of `F` at `x`.** Since `q i` is open (Proposition 3.2.7), `x` is
isolated in its fibre under `F` whenever `u` is isolated in its fibre under
`q i ≫ F`. By Corollary 3.1.10, `F` is then finite at `x` exactly when `x` lies
in the relative interior `Int(X/Y)`. The étale maps `q i` and `q i ≫ F` are
quasifinite, hence without boundary (Definition 3.1.1), so `u` lies in
`Int(U i/X)` and in `Int(U i/Y)`. Conrad–Temkin (2021), Lemma 2.9, applied to
`q i : U i → X` and `F : X → Y`, says that a point of `Int(U i/Y)` lying in
`Int(U i/X)` also lies in `(q i)⁻¹(Int(X/Y))`, with no hypothesis on `F`. Hence
`x ∈ Int(X/Y)`, and `F` is finite at `x`. The older forms of this
relative-interior formula assume more of `F`: local separatedness (Temkin,
Corollary 5.7), local separatedness and goodness (Berkovich 1993, Proposition
1.5.5(ii)), or good spaces (Berkovich 1990, Proposition 3.1.3(ii)).

Flatness and unramifiedness are then checked on finite affinoid models. The
remaining geometric work is to choose affinoid models of `F`, `q i` and
`q i ≫ F` around `x`, `u` and `F(x)` that fit together as follows.

**Algebraic descent on compatible finite affinoid models.** Suppose given
affinoid domains `W` of `Y`, `H` of `X` and `P` of `U i`, with `q i` mapping
`P` onto `H` and `F` mapping `H` into `W`. Suppose also that, for the bounded
maps of affinoid algebras `𝒲 → ℋ → 𝒫` they induce, `ℋ → 𝒫` and the composite
`𝒲 → 𝒫` are finite étale in the analytic sense: `𝒫` is a finite Banach algebra
over `ℋ` and over `𝒲` (Berkovich 1990, §2.1), and the underlying ring maps are
finite étale. Then `ℋ → 𝒫` is finite and flat with surjective map of spectra,
hence faithfully flat, and:
- Banach finiteness: `𝒲` is Noetherian and `ℋ` injects into the finite
  `𝒲`-module `𝒫`, so `ℋ` is a finite `𝒲`-module. This module finiteness is
  not enough. Over a trivially valued field it is weaker than finiteness as a
  Banach module (Berkovich 1990, the example after Proposition 2.1.9), and the
  comparison of differentials below concerns finite morphisms in the Banach
  sense. Banach finiteness descends through a retraction instead. The finite
  faithfully flat map `ℋ → 𝒫` has a bounded `ℋ`-linear retraction
  `r : 𝒫 → ℋ`. Choose an admissible epimorphism `𝒲ⁿ → 𝒫` sending the basis to
  `b₁, …, bₙ`. Every `y` in `ℋ` is then written in `𝒫` as `Σ cⱼ bⱼ` with
  `cⱼ ∈ 𝒲` of norm at most a constant times `‖y‖`, and applying `r` gives
  `y = Σ cⱼ r(bⱼ)`. So the map `𝒲ⁿ → ℋ` sending the basis to the `r(bⱼ)` is an
  admissible epimorphism, and `ℋ` is a finite Banach `𝒲`-algebra.
- Flatness: `𝒫` is flat over `𝒲` and faithfully flat over `ℋ`, so `ℋ` is flat
  over `𝒲`; Proposition 3.2.1 identifies this with flatness at the points.
- Unramifiedness: by Banach finiteness, `H → W`, `P → W` and `P → H` are
  finite morphisms of affinoid spaces, so their sheaves of differentials are
  given by the algebraic modules `Ω_{ℋ/𝒲}`, `Ω_{𝒫/𝒲}` and `Ω_{𝒫/ℋ}` (proof of
  Lemma 3.3.5). Proposition 3.3.2(i) gives only the right-exact sequence
  `𝒫 ⊗_ℋ Ω_{ℋ/𝒲} → Ω_{𝒫/𝒲} → Ω_{𝒫/ℋ} → 0`, and Proposition 3.3.3(i) compares
  differentials under Cartesian base change. The middle term vanishes because
  `𝒲 → 𝒫` is étale, but a surjection onto zero says nothing about its source.
  The further input is formal étaleness of `ℋ → 𝒫`: every `𝒲`-derivation of
  `ℋ` into a `𝒫`-module extends uniquely to `𝒫`, so the first map is an
  isomorphism `𝒫 ⊗_ℋ Ω_{ℋ/𝒲} ≅ Ω_{𝒫/𝒲} = 0`. Faithful flatness then gives
  `Ω_{ℋ/𝒲} = 0`.

So `F` is finite étale from `H` to `W`. The Library proves this algebraic
descent for bounded maps of affinoid algebras as
`Langlands.Analytic.BoundedAlgHom.finiteBanach_etale_of_finiteEtale_comp`
(module `Langlands.Geometry.Analytic.FiniteEtaleSourcePieces`). Banach
finiteness comes from the retraction argument above, proved as
`Langlands.Analytic.BoundedAlgHom.IsFiniteBanach.of_faithfullyFlat_comp` in the
same module, and the differentials from the isomorphism
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.

**The Library form of the pointwise argument.** The theorem
`Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteEtaleSourceNeighborhoods.isEtaleAtAllPieces`
(module `Langlands.Geometry.Analytic.FiniteEtaleSourceRecognition`) carries out
the argument above for strong maps `q : A → B` and `f : B → C` between
saturated presentations, with `q` and the composite étale over all pieces. At
a point `y` of `A`, `finiteEtaleSourceNeighborhoods` chooses open sets
`E ⊆ D` of `A` containing `y`, with `q` finite étale from `D` to an open set of
`B` and the composite finite étale from `E` to an open set `T` of `C`. The
theorem has a recognition hypothesis: for every recognized affinoid `W` of `C`
with locus in `T`, the set `q(E) ∩ f⁻¹(W)` is the locus of a recognized
affinoid `H` of `B`. This `H` is the middle model above. Given the hypothesis,
the algebraic descent makes `f` finite étale from `q(E)` to `T`, and the
theorem concludes that `f` is étale over all pieces at `q(y)`. The recognition
hypothesis is an additional premise of this theorem, absent from the
proposition stated here: it is where the Library form of the argument needs
the compatible models to be supplied.

**Transport through the localization.** A morphism of `LocalizedCategory` is
a right fraction whose denominator is a strong quasi-isomorphism, and `etale`
holds exactly when the numerator of a representing right fraction is étale
over all pieces; the choice of representative does not matter
(`localizedFractionEtale_eq_etale` and
`etale_localizationFunctor_map_iff_strongEtale` in the module
`Langlands.Geometry.Analytic.LocalizedEtaleComposition`,
`fractionEtale_localizedRightFraction_iff` in the module
`Langlands.Geometry.Analytic.SaturatedEtaleFractions`, all in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`). A proof can
represent `F` by a right fraction with denominator `s` and numerator `f`, and
each `q i ≫ s⁻¹` by a right fraction whose numerator `q' i` maps into the
source of `f`. Then `q' i` and `q' i ≫ f` are numerators of right fractions
representing the étale morphisms `q i ≫ s⁻¹` and `q i ≫ F`. The denominators
induce homeomorphisms of underlying spaces, so the point-coverage hypothesis
transfers, and the pointwise argument applies to `q' i` and `f` on the
saturation extensions where the strong étale property is tested. For a cover
by open domain inclusions this transport is carried out in
`Langlands.Analytic.SaturatedAtlasPresentation.etale_of_open_source_cover`
(module `Langlands.Geometry.Analytic.LocalizedEtaleSourceOpenLocality`), which
needs no recognition hypothesis.

## Provenance: derived

The proposition is a derived statement, not transcribed from a single theorem
of the sources: it is the source-locality of étaleness for the étale topology,
stated for the Library's localized category and its étale predicate. The
passages above fix the notions of finiteness, flatness, unramifiedness and
étaleness, their stability under composition, the composition formula for
relative interiors and the covering convention. The argument above explains
why the statement is expected to hold and is not a proof. In Berkovich's
category the finiteness step follows from Conrad–Temkin (2021), Lemma 2.9, without
hypotheses on `F`; the Library's pointwise theorem
`FiniteEtaleSourceNeighborhoods.isEtaleAtAllPieces` additionally assumes
recognition of the middle affinoid loci.

## Place in the Library

At universes `.{u, u, u}` the proposition is word for word the third premise of
`Langlands.Analytic.SpaceAnalytification.ExistenceReduction.SpaceAnalytificationExistenceFiveInputReductionStatement`,
so `LocalizedEtaleSourceDescentStatement.{u, u, u}` can be passed as that
premise of `spaceAnalytificationExistenceFiveInputReduction` without
conversion. At universes `.{u, u, u + 1}` it is the hypothesis of
`Langlands.Analytic.SpaceAnalytification.spaceAnalytificationEtaleStatement_of_sourceDescent`
(module `Langlands.Geometry.Analytic.SpaceAnalytificationEtaleFromSourceDescent`).
