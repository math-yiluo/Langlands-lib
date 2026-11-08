# Harris's inverse system `𝓛_m = 𝓛 / ℓ^m 𝓛` through forms, smooth forms, `Ext` and the hyperext abutments (Proposition 4.10)

Author: Worker 61. Built on Worker 61's module
`Langlands.Shimura.DefiniteFormsSmoothCoefficients` (candidate
`5582dec2-e211-422a-8821-c50815d036c5`), which has been independently
accepted but is not yet in the Library (commit c0c7eab6). From it this module
uses `coefficientDomain`, `domainLevel`, `awayLevel_domainLevel_le`,
`coefficientForms`, `coefficientTranslation`, `coefficientTransport`,
`coefficientFormsPresheaf`, `coefficientSmoothPresheaf`,
`coefficientExtPresheaf`, `coefficientAbutmentPresheaf`,
`coefficientFiltrationPresheaf`, `coefficientGradedPresheaf`,
`coefficientFiltrationι`, `coefficientFiltrationMapOfLE`,
`coefficientGradedπ`, `localCoefficientDomain`, `localCoefficientMap`,
`localCoefficientRep`, `dividingCoefficientDomain` and the
`dividingCoefficient*Presheaf`, `dividingCoefficientFiltrationι`,
`dividingCoefficientFiltrationMapOfLE` and `dividingCoefficientGradedπ`
specializations. That module imports two further accepted modules of
Worker 61 that are not yet in the Library:
`Langlands.Shimura.DefiniteFormsSmoothExt` (candidate
`687f402a-30ce-4e91-8e37-a5c30bf357a6`: `awayLevel`,
`factorHom_mul_awayLevel`) and
`Langlands.Cohomology.HyperextAbutmentFunctor` (candidate
`8e1ba75f-07ac-4edf-8a61-c381b99cc033`:
`HyperextAbutment.filtrationFunctor`, `gradedFunctor`, `filtrationι`,
`filtrationMapOfLE`, `gradedπ`). All three are included unchanged in this
candidate's workspace and must be integrated first.

It is also built on Worker 61's published
`Langlands.Shimura.EquivariantForms` (`formsRepFunctor`, `formsFunctor` and
the instance that `formsFunctor` preserves limits),
`Langlands.Cohomology.DivisibleSystem.Reduction` (`reductionTower`,
`reductionπ`) and `Langlands.Cohomology.DivisibleSystem.ReductionLimit`
(`reductionCone`, `isLimitReductionCone`); on Worker 13's published
`Langlands.Representation.Category.SmoothPartAdjunction`
(`SmoothRep.smoothPartFunctor`, `SmoothRep.toRepSmoothPartAdjunction`),
`Langlands.Cohomology.SmoothExt` (`SmoothExt.ext`),
`Langlands.Shimura.SplitLevelTower` (`factorHom`, `awayHom`) and
`Langlands.Shimura.Unitary.PointsSplit` (`DividingPoints`,
`finiteAdelicPointsSplit`); on Worker 41's published
`Langlands.Galois.CompatibleFamily`
(`GaloisRepresentation.residueCharacteristic`); on Worker 65's published
`Langlands.Global.CompletionResidue`
(`CompletionResidue.ringChar_residueField`,
`CompletionResidue.prime_ringChar_residueField`); and on Worker 57's
published `Langlands.Shimura.Levels` (`CompactOpenLevel`) and
`Langlands.Shimura.Unitary.Adelic` (`finiteAdelicDiagonal`). From Mathlib it
uses `Rep` with `Rep.resFunctor`, limits and limit preservation
(`limit.lift`, `limMap`, `Functor.mapCone`, `isLimitOfPreserves`,
`preservesLimits_of_evaluation`, `preservesLimits_of_reflects_of_preserves`,
`preservesLimits_of_natIso`, `Adjunction.rightAdjoint_preservesLimits`),
`Functor.flip` with `flipFunctor`, whiskering, `IsAdicComplete`, `ringChar`,
derived categories with their canonical t-structure (`singleFunctor`, shifts)
and `preadditiveCoyoneda`.

The accepted `DefiniteFormsSmoothCoefficients` constructs, for one
coefficient representation, the forms with coefficients as smooth
representations of the first factor, their `Ext` groups and the hyperext
abutment with its filtration, as presheaves on levels away from `p`. Harris
lets the coefficients run through the inverse system `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m`. This
module makes each of those presheaves functorial in the coefficients and
applies the result to the published reduction tower `m ↦ 𝓛 / l ^ m 𝓛`. This
gives presheaves of inverse systems over `m`, and comparison maps from the
terms for `𝓛` to the inverse limits of the terms for `𝓛_m`. For the forms and
the smooth forms it proves that these comparisons are limits when `𝓛` is
`l`-adically complete. Everything is first done for a group `G` with a
splitting `e : G ≃ₜ* H × H'` and a subgroup `D` of `G`, and then specialized
to Harris's `GJ(𝔸_f) ≃ GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})` with coefficients
pulled back along `g ↦ g_ℓ`.

## Conventions

`R` is a commutative ring. `Γ`, `G`, `H`, `H'` are groups, `ι : Γ →* G`, and
`G`, `H`, `H'` carry topologies. `e : G ≃ₜ* H × H'` is an isomorphism of
topological groups and `D` a subgroup of `G`. As in the accepted
`DefiniteFormsSmoothCoefficients`, for a representation `ρ` of `D` and a
subgroup `K'` of the coefficient domain `coefficientDomain e D` (the `k ∈ H'`
with `e⁻¹ (1, k) ∈ D`), `coefficientForms R e ι ρ K'` are the functions
`f : G → V` with `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)` for
`k ∈ e⁻¹ (1 × K')`, and `coefficientTranslation` is right translation by `H`
on them. The accepted presheaves `coefficientFormsPresheaf R e ι ρ`,
`coefficientSmoothPresheaf`, `coefficientExtPresheaf … W i`,
`coefficientAbutmentPresheaf … X n`, `coefficientFiltrationPresheaf … X n p`
and `coefficientGradedPresheaf … X n p` are functors out of
`(CompactOpenLevel (coefficientDomain e D))ᵒᵖ`. Their values at `K'` are
these forms as a representation of `H`, their smooth part `A(K')`,
`Ext^i(W, A(K'))`, `Hom(X, A(K')[n])`, and the step `F^p` and graded piece
`gr^p` of the abutment filtration on it. On arrows they are induced by
`coefficientTransport`.

For a natural number `ℓ` and an object `L` of an abelian category, the
published `reductionTower ℓ L : ℕᵒᵖ ⥤ C` is `m ↦ L / ℓ ^ m L` (the cokernel
of multiplication by `ℓ ^ m`) with the projections as transition maps,
`reductionπ ℓ L m : L ⟶ L / ℓ ^ m L` is the projection, and
`reductionCone ℓ L` is the cone over `reductionTower ℓ L` with vertex `L`
formed by these projections. The published `isLimitReductionCone` says that
this cone is a limit when `L` is complete for the `ℓ`-adic topology
(`IsAdicComplete (Ideal.span {(ℓ : R)}) L`).

An "inverse system" is a functor `ℕᵒᵖ ⥤ C`. A "bifunctor" here is a functor
from coefficients to presheaves on levels. For such a bifunctor `B` and an
inverse system `L` of coefficients, `(L ⋙ B).flip` is the presheaf on levels
of inverse systems `K' ↦ (m ↦ B (L m) K')`.

## Generic declarations

Namespace `Langlands.Shimura.EquivariantForms`.

Section `Functoriality` (universes arbitrary; coefficients in `Rep.{t} R D`,
forms in `Rep.{max uG t} R H`):

- `coefficientRepFunctor R e ι K' : Rep R D ⥤ Rep R H`, for a subgroup `K'`
  of the coefficient domain: Mathlib's restriction from `D` to
  `e⁻¹ (1 × K')` followed by the published `formsRepFunctor` (forms with
  right translation along `factorHom e`). Its object at `X` is
  `Rep.of (coefficientTranslation R e ι X.ρ K')`
  (`coefficientRepFunctor_obj`, true by definition), and a morphism `φ` acts
  by `f ↦ φ ∘ f` (`coefficientRepFunctor_map_apply_coe`).
- `coefficientTransport_comp_map`: postcomposition with `φ : X ⟶ Y` commutes
  with `coefficientTransport` along any `c`, because `φ` intertwines the
  actions of `c` on `X` and `Y`.
- `coefficientFormsBifunctor R e ι`: the functor
  `X ↦ coefficientFormsPresheaf R e ι X.ρ` from `Rep R D` to presheaves of
  representations of `H`; at a level `K'` its map is
  `coefficientRepFunctor … K'` applied to `φ`, natural in `K'` by
  `coefficientTransport_comp_map` (`coefficientFormsBifunctor_obj`,
  `coefficientFormsBifunctor_map_app`).
- With `[IsTopologicalGroup H]`: `coefficientSmoothBifunctor R e ι`,
  `coefficientFormsBifunctor` followed levelwise by
  `SmoothRep.smoothPartFunctor`; its object at `X` is
  `coefficientSmoothPresheaf R e ι X.ρ` (`coefficientSmoothBifunctor_obj`).
- `coefficientFormsSystem R e ι L`, `coefficientSmoothSystem R e ι L`: for an
  inverse system `L : ℕᵒᵖ ⥤ Rep R D`, the presheaves of inverse systems
  `K' ↦ (m ↦ forms (smooth forms) of level e⁻¹ (1 × K') with coefficients L m)`.

Section `Limits` (coefficients and forms in `Rep.{max uG t}`, so that the
forms functor stays in one universe):

- `formsRepFunctorCompForget₂Iso`: `formsRepFunctor` followed by the
  forgetful functor to `ModuleCat R` is the published `formsFunctor` (the
  components are identities).
- Instance `formsRepFunctor_preservesLimits`: `formsRepFunctor` preserves
  limits, because after the forgetful functor, which preserves and reflects
  limits, it is `formsFunctor`, which preserves limits by a published
  instance.
- Instance `coefficientRepFunctor_preservesLimits`: the composite of
  Mathlib's restriction and `formsRepFunctor` preserves limits.
- Instances `coefficientFormsBifunctor_preservesLimits`,
  `coefficientSmoothBifunctor_preservesLimits` (with
  `[IsTopologicalGroup H']`, and `[IsTopologicalGroup H]` for the smooth
  case): limits in presheaf categories are computed levelwise
  (`preservesLimits_of_evaluation`); at each level the functor is
  `coefficientRepFunctor`, followed in the smooth case by
  `SmoothRep.smoothPartFunctor`, a right adjoint by the published
  `SmoothRep.toRepSmoothPartAdjunction`.
- `isLimitCoefficientFormsReductionCone R e ι ℓ hL`,
  `isLimitCoefficientSmoothReductionCone R e ι ℓ hL`: for a natural number
  `ℓ` and `hL : IsAdicComplete (Ideal.span {(ℓ : R)}) L`, the image under
  `coefficientFormsBifunctor` (resp. `coefficientSmoothBifunctor`) of
  `reductionCone ℓ L` is a limit cone. That is, the presheaf of forms
  (smooth forms) with coefficients `L` is the inverse limit of the presheaves
  of forms (smooth forms) with coefficients `L / ℓ ^ m L`, via the maps
  induced by the projections. Proof: the bifunctor preserves limits and the
  published `isLimitReductionCone` applies.

Section `CoefficientExt`: `R`, `G`, `H` and the coefficients lie in one
universe `u`, as the published smooth `Ext` requires, and `H` is a
topological group.

- `coefficientExtBifunctor R e ι W i`: `coefficientSmoothBifunctor` followed
  levelwise by `SmoothExt.ext R H W i`; its object at `X` is
  `coefficientExtPresheaf R e ι X.ρ W i` (`coefficientExtBifunctor_obj`).
- `coefficientExtSystem R e ι W i L`: the presheaf of inverse systems
  `K' ↦ (m ↦ Ext^i(W, A_{L m}(K')))`.
- `coefficientExtReductionComparison R e ι W i ℓ L`: the map from
  `coefficientExtPresheaf` for `L` to the limit over `m` of the presheaves
  for `L / ℓ ^ m L`, the `limit.lift` of the image of `reductionCone ℓ L`.
  `coefficientExtReductionComparison_π`: followed by the projection to the
  `m`-th term it is the bifunctor applied to `reductionπ ℓ L m`.

With `[HasDerivedCategory.{w} (SmoothRep R H)]` and an object `X` of the
derived category (`n` a total degree, `p` a filtration index):

- `coefficientAbutmentBifunctor R e ι X n`,
  `coefficientFiltrationBifunctor R e ι X n p`,
  `coefficientGradedBifunctor R e ι X n p`: `coefficientSmoothBifunctor`
  followed levelwise by `singleFunctor _ 0` and then by the shift by `n` and
  `preadditiveCoyoneda.obj (op X)`, resp. the accepted
  `HyperextAbutment.filtrationFunctor` and `gradedFunctor`. Their objects at
  `Y` are the accepted `coefficientAbutmentPresheaf`,
  `coefficientFiltrationPresheaf` and `coefficientGradedPresheaf` for `Y.ρ`
  (`_obj` lemmas, true by definition).
- `coefficientFiltrationBifunctorι`, `coefficientFiltrationBifunctorMapOfLE`
  (for `p ≤ q`), `coefficientGradedBifunctorπ`: the inclusions
  `F^p ⟶ Hom(X, A(K')[n])`, `F^q ⟶ F^p` and the projections `F^p ⟶ gr^p`
  as natural transformations of bifunctors (the accepted `filtrationι`,
  `filtrationMapOfLE` and `gradedπ`, whiskered). Their components at `Y` are
  the accepted `coefficientFiltrationι`, `coefficientFiltrationMapOfLE` and
  `coefficientGradedπ` for `Y.ρ` (`_app` lemmas, true by definition).
- `coefficientAbutmentSystem`, `coefficientFiltrationSystem`,
  `coefficientGradedSystem`, for an inverse system `L` of coefficients, with
  the morphisms `coefficientFiltrationSystemι`,
  `coefficientFiltrationSystemMapOfLE` and `coefficientGradedSystemπ` of
  presheaves of inverse systems (the natural transformations above whiskered
  by `L` and flipped by `flipFunctor`).
- `coefficientAbutmentReductionComparison`,
  `coefficientFiltrationReductionComparison`,
  `coefficientGradedReductionComparison`, with their `_π` lemmas: the
  comparison maps to the limits over `m` of the terms for `L / ℓ ^ m L`, as
  for `Ext`.
- `coefficientFiltrationReductionComparison_ι`,
  `coefficientFiltrationReductionComparison_gradedπ`: the comparison maps
  commute with the inclusions `F^p ⟶ Hom(X, A(K')[n])` and with the
  projections `F^p ⟶ gr^p`, the maps between the limits being `limMap` of
  the natural transformations. The proofs check this after each projection
  of the limit, using the naturality of the transformations.

## Harris's case

Namespace `Langlands.Shimura.DefiniteForms`.

Section `ResidueCharacteristic`, for a finite place `ℓ` of `ℚ` and
`l = GaloisRepresentation.residueCharacteristic ℓ`, the characteristic of
`𝓞 ℚ ⧸ ℓ.asIdeal` (published):

- `residueCharacteristic_prime`: `l` is prime. It equals the characteristic
  of the residue field of the completion at `ℓ`
  (`CompletionResidue.ringChar_residueField`), which is prime
  (`CompletionResidue.prime_ringChar_residueField`).
- Instance `residueCharacteristic_neZero`: `l ≠ 0`.
- `natCast_residueCharacteristic_mem`: `(l : 𝓞 ℚ) ∈ ℓ.asIdeal`, since `l`
  maps to `0` in `𝓞 ℚ ⧸ ℓ.asIdeal`. This is the hypothesis `hℓ` of the
  published completeness theorems of `DivisibleSystem.HarrisLatticeLimit`
  (`isAdicComplete_harrisCoefficientIntegers`, `isAdicComplete_harrisLattice`,
  `isAdicComplete_stableCoefficientLattice`), taken with their natural
  number equal to `l` and their place equal to `ℓ`. Those theorems give the
  `l`-adic completeness of the underlying modules of Harris's coefficient
  rings and lattices, which is the form of the hypothesis `h𝓛` below. This
  module does not build representations of `Kℓ` from those lattices.

Section `DividingSystem`. `A` is a finite-dimensional `ℚ`-algebra with
involution `σ : AlgebraInvolution ℚ A`, `ℓ` a finite place of `ℚ`, `Kℓ` a
subgroup of `σ.Points (FiniteCompletion ℚ ℓ)` (Harris's `K_ℓ`; no topological
condition is imposed), `R` a commutative ring, and `p : ℕ` with `hp : p ≠ 0`.
`A`, `R` and the coefficients lie in one universe `u`. The generic
declarations are applied with `e = σ.finiteAdelicPointsSplit p hp`
(`GJ(𝔸_f) ≃ₜ* GJ(∏_{v ∣ p} ℚ_v) × GJ(𝔸_f^{(p)})`),
`ι = σ.finiteAdelicDiagonal` and `D = localCoefficientDomain σ ℓ Kℓ` (the
`g ∈ GJ(𝔸_f)` with `g_ℓ ∈ Kℓ`). Levels `K'` are compact open levels of the
accepted `dividingCoefficientDomain σ ℓ Kℓ p hp`. Write `𝓛_m` for
`(reductionTower l 𝓛).obj (op m) = 𝓛 / l ^ m 𝓛`.

- `localCoefficientFunctor σ ℓ Kℓ R` (abbreviation): Mathlib's
  `Rep.resFunctor` along the accepted `localCoefficientMap σ ℓ Kℓ`
  (`g ↦ g_ℓ`), from `Rep R Kℓ` to `Rep R (localCoefficientDomain σ ℓ Kℓ)`;
  `localCoefficientFunctor_obj_ρ`: the restricted representation of `𝓛` is
  the accepted `localCoefficientRep σ ℓ Kℓ 𝓛.ρ`.
- `dividingCoefficientFormsBifunctor σ ℓ Kℓ R p hp`,
  `dividingCoefficientSmoothBifunctor`,
  `dividingCoefficientExtBifunctor … W i`: `localCoefficientFunctor` followed
  by the generic bifunctors. Their objects at `𝓛 : Rep R Kℓ` are
  `coefficientFormsPresheaf` for `localCoefficientRep σ ℓ Kℓ 𝓛.ρ`, the
  accepted `dividingCoefficientSmoothPresheaf σ ℓ Kℓ 𝓛.ρ p hp` and
  `dividingCoefficientExtPresheaf σ ℓ Kℓ 𝓛.ρ p hp W i` (`_obj` lemmas, true
  by definition).
- `dividingReductionFormsSystem σ ℓ Kℓ R p hp 𝓛`,
  `dividingReductionSmoothSystem`, `dividingReductionExtSystem … W i 𝓛`:
  `(reductionTower l 𝓛 ⋙ B).flip` for these bifunctors `B`, the presheaves
  of inverse systems `K' ↦ (m ↦ B(𝓛_m)(K'))`.
  `dividingReductionFormsSystem_eq` (true by definition): the first is the
  generic `coefficientFormsSystem` of the inverse system
  `reductionTower l 𝓛 ⋙ localCoefficientFunctor σ ℓ Kℓ R`.
- `dividingReductionExtComparison σ ℓ Kℓ R p hp W i 𝓛` with
  `dividingReductionExtComparison_π`: the map from
  `dividingCoefficientExtPresheaf` for `𝓛` to the limit over `m` of those
  for `𝓛_m`, induced by the projections `𝓛 ⟶ 𝓛_m`.
- With `[HasDerivedCategory.{w} (SmoothRep R (σ.DividingPoints p))]`, an
  object `X` of the derived category, a total degree `n` and filtration
  indices `i ≤ j` (section `DividingAbutment`):
  `dividingCoefficientAbutmentBifunctor`,
  `dividingCoefficientFiltrationBifunctor`,
  `dividingCoefficientGradedBifunctor` (objects at `𝓛`: the accepted
  `dividingCoefficientAbutmentPresheaf`, `dividingCoefficientFiltrationPresheaf`
  and `dividingCoefficientGradedPresheaf` for `𝓛.ρ`);
  `dividingCoefficientFiltrationBifunctorι`,
  `dividingCoefficientFiltrationBifunctorMapOfLE`,
  `dividingCoefficientGradedBifunctorπ` (components at `𝓛`: the accepted
  `dividingCoefficientFiltrationι`, `dividingCoefficientFiltrationMapOfLE`,
  `dividingCoefficientGradedπ`); the systems
  `dividingReductionAbutmentSystem`, `dividingReductionFiltrationSystem`,
  `dividingReductionGradedSystem` with the morphisms
  `dividingReductionFiltrationSystemι`,
  `dividingReductionFiltrationSystemMapOfLE`,
  `dividingReductionGradedSystemπ`; the comparison maps
  `dividingReductionAbutmentComparison`,
  `dividingReductionFiltrationComparison`,
  `dividingReductionGradedComparison` with their `_π` lemmas; and
  `dividingReductionFiltrationComparison_ι`,
  `dividingReductionFiltrationComparison_gradedπ` (compatibility with the
  inclusions and projections of the filtration).
- Instances `dividingCoefficientFormsBifunctor_preservesLimits`,
  `dividingCoefficientSmoothBifunctor_preservesLimits`: composites of
  Mathlib's restriction and the generic bifunctors.
- `isLimitDividingCoefficientFormsReductionCone σ ℓ Kℓ p hp h𝓛`,
  `isLimitDividingCoefficientSmoothReductionCone σ ℓ Kℓ p hp h𝓛`: for
  `h𝓛 : IsAdicComplete (Ideal.span {(l : R)}) 𝓛`, the presheaf of forms
  (resp. the accepted `dividingCoefficientSmoothPresheaf`) with coefficients
  `𝓛` is the inverse limit of those with coefficients `𝓛_m`, via the maps
  induced by the projections `𝓛 ⟶ 𝓛_m`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4. Worker 61 read the rendered scanned
pages.

- Printed p.309 (one-based PDF page 11): "Let `𝓛` be a free `𝒪/ℓ^m 𝒪`-module,
  and let `𝓛̃` denote the corresponding constant étale sheaf on
  `S(GG, X_{n-1})_{K(N,m)}`. Write `𝒪_m = 𝒪/ℓ^m 𝒪`."
- Printed p.311 (one-based PDF page 13), after (4.9): "Now we want to let `m`
  vary. Let the `K_ℓ`-modules `(ρ, W)` and `𝓛 = 𝓛_W` be as in §3; let
  `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any `m`. Then `𝓛_m` forms an inverse system of
  `𝒪`-modules, and the inverse system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf
  `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_{K(N)}`." Then Proposition 4.10 (quoted in the
  accepted `DefiniteFormsSmoothCoefficients.md`), whose proof begins: "We need
  to check that the complexes used to obtain the spectral sequences (4.9)
  satisfy a Mittag-Leffler condition as `m` varies."

How the module relates to Harris (an explanation, not formalized):

- The prime. Harris's `ℓ` is a rational prime. In the Library the coefficient
  place is a finite place `ℓ` of `ℚ`, and Harris's prime is its residue
  characteristic `l`. The reductions are taken modulo `l ^ m`, which is
  Harris's `ℓ^m`. `residueCharacteristic_prime` and
  `natCast_residueCharacteristic_mem` record the facts needed to connect this
  `l` with the published completeness theorems for Harris's lattices.
- The inverse system. Harris's `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` with `𝒪_m = 𝒪/ℓ^m 𝒪` is
  `𝓛 / ℓ^m 𝓛`, which is the published `reductionTower l 𝓛` evaluated at `m`
  (the cokernel of multiplication by `l ^ m`), with the projections as
  transition maps. Here `𝓛` is any representation of `Kℓ` over any
  commutative ring `R`; Harris's case is `R = 𝒪` and `𝓛` a `K_ℓ`-stable
  lattice, with `K_ℓ` acting on `𝓛_m` through the quotient action.
- Taking the system through the forms. Harris's finite-level spectral
  sequences (4.9) have second argument built from `𝒜_ℓ(GJ, 𝓛_m, H(m))`, and
  his limit (4.10.1) has `𝒜_ℓ(GJ, ρ, H)`. The accepted
  `DefiniteFormsSmoothCoefficients` constructs the forms with coefficients
  `𝓛 (g_ℓ)` as smooth `GJ(∏_{v ∣ p} ℚ_v)`-modules, their `Ext` groups and the
  hyperext abutment for one coefficient representation. This module makes
  them functorial in the coefficient representation and evaluates them on
  `m ↦ 𝓛_m`. The resulting `dividingReduction*System`s are presheaves on
  levels away from `p` of inverse systems indexed by `m`; the level
  variation is that of the accepted module.
- The limit. Harris passes to the limit in `m` by a Mittag-Leffler argument
  on the complexes computing (4.9). This module proves the limit statement
  only for the forms and the smooth forms
  (`isLimitDividingCoefficient{Forms,Smooth}ReductionCone`), from the
  published `isLimitReductionCone` and preservation of limits. For `Ext`,
  the abutments, filtration steps and graded pieces it defines the
  comparison maps `dividingReduction*Comparison` from the term for `𝓛` to the
  inverse limit of the terms for `𝓛_m` and proves that they commute with the
  projections and with the maps of the filtration. It does not prove that
  they are isomorphisms. Mittag-Leffler conditions and `lim¹` terms are not
  treated.
- Coefficient rings. Harris's (4.10.1) uses `L_ℓ`-coefficients (after
  inverting `ℓ`), while the system `𝓛_m` consists of `𝒪`-modules. Here all
  terms are over the one ring `R`; inverting `l` is not formalized.
- All declarations are ours, derived from Mathlib and the published and
  accepted modules named above. The bifunctors, systems and comparison maps
  are internal constructions not printed in Harris 1999. The generic
  sections allow any natural number `ℓ` in the reduction tower; Harris's case
  uses the residue characteristic `l`.

## Related declarations

- Library `Langlands.Cohomology.DivisibleSystem.ReductionLimit`
  (`isLimitReductionCone`, `ihomReductionLimitIso`,
  `permutationIhomReductionLimitIso`): the limit statements for the
  coefficients themselves and for Harris's `Hom(𝒪_m[C_p/H_p]^M, 𝓛_m)` of
  (4.8). This module transports `isLimitReductionCone` through the forms.
- Library `Langlands.Cohomology.DivisibleSystem.HarrisLatticeLimit`: the
  `ℓ`-adic completeness of Harris's coefficient rings and lattices, whose
  hypothesis `natCast_residueCharacteristic_mem` supplies for `l`.
- `Langlands.Shimura.DefiniteForms.dividingExtHeckeAlgebraHom`
  (`Shimura/DefiniteFormsHeckeExt`, accepted, not yet in the Library; in this
  workspace but not imported): Hecke operators for trivial coefficients. Hecke
  operators on the systems of this module are not treated.

## Scope

The module provides the forms with coefficients, their smooth parts, their
`Ext` groups and the hyperext abutments with their filtrations as functors of
the coefficient representation; Harris's inverse system `m ↦ 𝓛_m` taken
through them as presheaves of inverse systems; the comparison maps to the
inverse limits; and the limit statement for forms and smooth forms when `𝓛`
is `l`-adically complete. It does not:

- prove that the comparison maps for `Ext`, the abutments, filtration steps
  or graded pieces are isomorphisms, or any Mittag-Leffler property;
- construct the spectral sequence (4.10.1), the lisse sheaves `𝓛̃_m` and
  `W̃`, `M̌_N` or the Shimura varieties, or prove (4.8), (4.9) or any
  convergence or comparison with the cohomology of `S̄_{K(N)}`;
- invert `l` or pass to `L_ℓ`-coefficients;
- treat Hecke operators or Galois actions on these systems.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published and accepted modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
