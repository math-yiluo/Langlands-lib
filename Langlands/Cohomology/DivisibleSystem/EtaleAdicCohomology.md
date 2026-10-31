# `ℓ`-adic étale cohomology as an inverse limit of cohomology modules

Author: Worker 61. Built on the published modules
`Langlands.Geometry.EtaleDerivedSections` of Worker 13 (`ModuleSheaf`,
`sections`, `cohomology`, `cohomologyZeroIso`, `diagramFunctor`),
`Langlands.Geometry.EtaleAdicSystem` of Worker 13 (`functor`,
`inverseLimit`), `Langlands.Geometry.EtaleActionFunctor`
(`EtaleCohomologyAction.pullbackCohomologyFunctor`,
`pullbackSectionsFunctor`, `pullbackCohomologyZeroFunctorIso`),
`Langlands.Geometry.EtaleEquivariantAdicSystem`
(`EtaleAdicSystem.equivariantFunctor`,
`EtaleAdicSystem.equivariantFunctorForgetIso`),
`Langlands.Cohomology.DivisibleSystem.HarrisEtale`
(`harrisEtaleDivisibleSystem`, `harrisEtaleSectionsDivisibleSystem`) and
`Langlands.Cohomology.DivisibleSystem.InverseLimit` (`inverseLimit`, the
limit of the tower of an `ℓ`-divisible system). Through their imports it uses
Worker 13's `EtaleCohomologyAction.EquivariantSheaf` and
`TranslationAction.Equivariant.forget`
(`Langlands.Geometry.EtaleCohomologyAction`,
`Langlands.Cohomology.TranslationAction`) and Worker 13's
`harrisEtaleCoefficientSystem`, `harrisEtaleCohomologySystem`,
`harrisEtaleSectionsSystem` and `harrisEtaleCohomologyZeroIso`
(`Langlands.Shimura.Coefficients.HarrisEtaleCoefficients`). From Mathlib it
uses `lim`, `limit.π`, `limit.w`, `limit.hom_ext`, `limMap_π`,
`limit.post`, `limit.post_π`, `limit.map_post`, `preservesLimitNatIso`,
`preservesLimitIso_hom_π`, `preservesLimitsOfShape_of_natIso`,
`NatIso.isIso_of_isIso_app`, `Functor.whiskeringRight`, `Action.forget`
(which preserves limits), `CategoryTheory.Sheaf.Γ` and the adjunction
`constantSheafΓAdj`.

Everything is in the namespace `Langlands.Cohomology.EtaleAdicCohomology`.
Composition `f ≫ g` is `f` followed by `g`.

## Conventions

`X : Scheme.{u}` is a scheme and `R : Type u` a commutative ring. A sheaf
is a sheaf of `R`-modules on the small étale site of `X`
(`EtaleDerivedSections.ModuleSheaf X R`). `Γ(X, -)` is the published global
sections functor `EtaleDerivedSections.sections X R`, and `H^q(X, -)` is the
published `EtaleDerivedSections.cohomology X R q`, the `q`-th right derived
functor of `Γ(X, -)`; the published `cohomologyZeroIso` identifies `H^0`
with `Γ`. An inverse system is a functor `F : ℕᵒᵖ ⥤ Sheaf`, with objects
`F_m` and maps `F_n ⟶ F_m` for `m ≤ n`. `lim` is Mathlib's limit functor;
all limits below are over `ℕᵒᵖ`.

## Inverse limits of cohomology modules

- `adicCohomology X R q`: the functor sending an inverse system `F` to
  `lim_m H^q(X, F_m)`, that is, the published `diagramFunctor`
  (`H^q(X, -)` applied to every `F_m`) followed by `lim`
  (`adicCohomology_obj`, by definition).
- `adicCohomologyπ q F n : lim_m H^q(X, F_m) ⟶ H^q(X, F_n)`: the limit
  projection. `adicCohomologyπ_map`: it is compatible with the maps
  `H^q(X, F_n) ⟶ H^q(X, F_m)` for `m ≤ n`; `map_adicCohomologyπ`: it is
  natural in `F`; `adicCohomology_hom_ext`: morphisms into
  `lim_m H^q(X, F_m)` agreeing after every projection are equal.
- `adicSections X R`: the functor `F ↦ lim_m Γ(X, F_m)`.
  `adicCohomologyZeroIso X R : adicCohomology X R 0 ≅ adicSections X R`:
  `lim` of the published `cohomologyZeroIso` applied levelwise.
- Global sections are a right adjoint, of the constant sheaf functor
  (instance, from Mathlib's `CategoryTheory.Sheaf.Γ`), so they preserve
  limits. `limitSectionsIso X R : Γ(X, lim_m F_m) ≅ lim_m Γ(X, F_m)`,
  natural in `F`, is Mathlib's `preservesLimitNatIso`.
- `limitComparison X R q : H^q(X, lim_m F_m) ⟶ lim_m H^q(X, F_m)`, natural
  in `F`: the canonical map `limit.post`, whose projections are the maps
  `H^q(X, lim_m F_m) ⟶ H^q(X, F_n)` induced by the limit projections
  (`limitComparison_π`).
- `limitComparison_zero`: in degree zero, `limitComparison X R 0` followed by
  `adicCohomologyZeroIso` equals `cohomologyZeroIso` at `lim_m F_m` followed
  by `limitSectionsIso`. Proof: after each projection, both sides are the map
  induced by a limit projection, by naturality of `cohomologyZeroIso`.
- `H^0(X, -)` preserves limits over `ℕᵒᵖ`, being isomorphic to `Γ(X, -)`
  (instance), and therefore `limitComparison X R 0` is an isomorphism
  (instance; each component is `limit.post` of a limit-preserving functor).

Nothing is stated about `limitComparison X R q` for `q > 0`; Milne notes
that `H^r(X, lim F_n)` and `lim H^r(X, F_n)` differ in general.

## Ideal-adic reductions

`I` is an ideal of `R`. For a sheaf `F`, the published
`EtaleAdicSystem.functor X I` is the inverse system `n ↦ F / I ^ n F` of
sheafified sectionwise reductions, as sheaves of `R`-modules, and
`EtaleAdicSystem.inverseLimit X I F` is its limit sheaf.

- `idealAdicCohomology I q`: the functor `F ↦ lim_n H^q(X, F / I ^ n F)`,
  that is, `EtaleAdicSystem.functor X I` followed by `adicCohomology X R q`
  (`idealAdicCohomology_obj`, by definition).
- `idealAdicCohomologyZeroIso I`: in degree zero,
  `lim_n H^0(X, F / I ^ n F) ≅ Γ(X, lim_n F / I ^ n F)`, naturally in `F`
  (`adicCohomologyZeroIso` followed by the inverse of `limitSectionsIso`).
  `idealAdicCohomologyZeroInverseLimitIso I F`: its component at `F`, with
  target the sections of the published sheaf
  `EtaleAdicSystem.inverseLimit X I F`.
- `idealLimitComparison I q`: the comparison
  `H^q(X, lim_n F / I ^ n F) ⟶ lim_n H^q(X, F / I ^ n F)`, natural in `F`,
  the comparison `limitComparison` at the system of reductions.

## Equivariant coefficients

`G` is a group and `ρ : G →* (Aut X)ᵐᵒᵖ` an action of `G` on `X` by
automorphisms. A `ρ`-equivariant sheaf (Worker 13's
`EtaleCohomologyAction.EquivariantSheaf R ρ`) is a sheaf with compatible
structure maps from its translates under `G`;
`TranslationAction.Equivariant.forget` forgets the structure maps. The
published `pullbackCohomologyFunctor R ρ q` sends a `ρ`-equivariant sheaf to
`H^q(X, F)` with its action of `G`, an object of
`Action (ModuleCat R) G`, and `pullbackSectionsFunctor R ρ` does the same for
`Γ(X, F)`.

- `equivariantAdicCohomology R ρ q`: the functor sending an inverse system of
  `ρ`-equivariant sheaves to `lim_m H^q(X, F_m)` as a representation of `G`,
  the limit in `Action (ModuleCat R) G` of the representations
  `pullbackCohomologyFunctor R ρ q` of the `F_m`.
- `equivariantAdicCohomologyForgetIso R ρ q`: the underlying module of
  `equivariantAdicCohomology R ρ q` of `F` is `adicCohomology X R q` of the
  underlying inverse system of sheaves, naturally in `F`. `Action.forget`
  preserves limits (`preservesLimitNatIso`), and the underlying module of
  `pullbackCohomologyFunctor R ρ q` of a sheaf is, by definition, its
  cohomology module.
- `equivariantAdicSections R ρ`: `lim_m Γ(X, F_m)` as a representation of
  `G`. `equivariantAdicCohomologyZeroIso R ρ`: in degree zero
  `equivariantAdicCohomology R ρ 0 ≅ equivariantAdicSections R ρ`, `lim` of
  the published `pullbackCohomologyZeroFunctorIso` applied levelwise.
- `equivariantIdealAdicCohomology ρ I q`: for a `ρ`-equivariant sheaf `F`,
  `lim_n H^q(X, F / I ^ n F)` as a representation of `G`, using the
  published equivariant reductions `EtaleAdicSystem.equivariantFunctor I ρ`.
  `equivariantIdealAdicCohomologyForgetIso ρ I q`: its underlying module is
  `idealAdicCohomology I q` of the underlying sheaf, naturally in `F`
  (`equivariantAdicCohomologyForgetIso` and the published
  `equivariantFunctorForgetIso`).

## Harris's coefficient sheaves

As in the published `HarrisEtale` and `HarrisEtaleCoefficients`, `ℓ` is a
natural number, `A` a finite-dimensional `ℚ`-algebra with Worker 13's
involution `σ`, `L` a number field, `W` a finite-dimensional `L`-module with
an algebraic representation `ρ` of `σ.baseChange L`, `p` a finite place of
`ℚ` and `U` a compact open level of `σ.FiniteAdelicPoints`;
`R = HarrisCoefficientIntegers L p`, `𝓛` is the stable Harris lattice, and
`Y : EquivariantDiagram (harrisCongruenceGroups ρ p U ℓ) X.Etale` with
`hY : ∀ n, IsFiniteGeometricTorsor X (Y.action n)`. The published
`harrisEtaleCoefficientSystem ρ p U ℓ X Y hY` is the inverse system of
étale sheaves associated to `𝓛 / ℓ ^ m 𝓛` on the torsors `Y m`; write
`𝓛̃_m` for its objects.

- `harrisEtaleAdicCohomology ℓ ρ p U X Y hY q`: `lim_m H^q(X, 𝓛̃_m)`, the
  value of `adicCohomology` at `harrisEtaleCoefficientSystem`.
  `harrisEtaleAdicCohomology_eq`: it is, by definition, the limit of the
  published `harrisEtaleCohomologySystem ρ p U ℓ X Y hY q`.
- `harrisEtaleAdicCohomologyZeroIso`: in degree zero,
  `lim_m H^0(X, 𝓛̃_m) ≅ lim_m Γ(X, 𝓛̃_m)`, the limit of the published
  `harrisEtaleSectionsSystem`; `lim` of the published
  `harrisEtaleCohomologyZeroIso`.
- `harrisEtaleAdicCohomologyZeroLimitIso`: in degree zero,
  `lim_m H^0(X, 𝓛̃_m) ≅ Γ(X, lim_m 𝓛̃_m)` (`adicCohomologyZeroIso` followed by
  the inverse of `limitSectionsIso`).
- `harrisEtaleAdicCohomologyZeroDivisibleIso`, for `[NeZero ℓ]` and the
  hypothesis `hΓ` of the published `harrisEtaleSectionsDivisibleSystem`
  (global sections of every map `j` of `harrisEtaleDivisibleSystem` are
  epimorphisms): degree-zero cohomology is the inverse limit of the
  `ℓ`-divisible system `harrisEtaleSectionsDivisibleSystem`. Its tower is, by
  definition, `harrisEtaleSectionsSystem`, so the isomorphism is
  `harrisEtaleAdicCohomologyZeroIso`.

## Provenance and interpretation

Milne, *Étale Cohomology* (1980), Chapter V, §1 (Worker 61 read the text
layer of the scanned pages):

- printed p.163 (one-based PDF page 177), paraphrased: for a prime `l`, an
  `l`-adic sheaf on `X_et` is a projective system `F = (F_n)_{n∈ℕ}` of
  sheaves such that each map `F_{n+1} → F_n` induces an isomorphism
  `F_{n+1}/l^n F_{n+1} ≅ F_n`;
- printed p.164 (one-based PDF page 178): "It follows that `F_0 = 0` and
  `F_n` is killed by `l^n`, that is, that it is a `Z/(l^n)`-module. The
  cohomology groups of an `l`-adic sheaf `F` are defined to be
  `H^r(X, F) = lim H^r(X, F_n)`. Note that `H^r(X, F) ≠ H^r(X, lim F_n)` in
  general, even for `r = 1` and `X` the spectrum of a field."

`adicCohomology X R r` is Milne's `lim H^r(X, F_n)` for any inverse system
of sheaves of `R`-modules; Milne's `l`-adic sheaves are the special case of
inverse systems satisfying his condition, which is not imposed here. An
`l`-adic sheaf, viewed as an inverse system of sheaves of modules over `ℤ`
(`ULift ℤ` for schemes in higher universes), gives `adicCohomology`
corresponding to Milne's `H^r(X, F)` through the identification of
`ℤ`-modules with abelian groups, which is not formalized here; on p.163
Milne recalls (III.2.25) that the cohomology of a sheaf of `Z/(n)`-modules
agrees with its cohomology as a sheaf of `Z`-modules. `limitComparison` is the canonical map
`H^r(X, lim F_n) ⟶ lim H^r(X, F_n)` between the two sides of Milne's remark;
the module proves only that it is an isomorphism for `r = 0`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4 (Worker 61 read the rendered scanned
pages):

- printed p.311 (one-based PDF page 13): "the inverse system `{𝓛̃_m}`
  defines a lisse `ℓ`-adic sheaf `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on `S̄_{K(N)}`";
- printed p.312 (one-based PDF page 14), end of the proof of
  Proposition 4.10: "In fact, we have proved the stronger (integral)
  statement (4.10.4)
  `E_2^{i,j} = Ext^i(H_c^{2(n−1)−j}(M̆_N, 𝒪(n − 1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒
  H^{i+j}(S̄_{K(N)}, 𝓛̃)`."

Harris does not define `H^{i+j}(S̄_{K(N)}, 𝓛̃)` on these pages; we read it with
Milne's definition as `lim_m H^{i+j}(S̄_{K(N)}, 𝓛̃_m)`.
`harrisEtaleAdicCohomology` is this limit for the
published model `harrisEtaleCoefficientSystem` of `{𝓛̃_m}`, over an input
scheme `X` with input torsors `Y`, with the qualifications recorded in the
published `HarrisEtaleCoefficients` and `HarrisEtale`: `X`, `Y` and `hY` are
not identified with Harris's `S̄_{K(N)}` and its covers of level `K(N, m)`,
and `ℓ` and `p` are unrelated inputs.

The ideal-adic and equivariant variants, the degree-zero identifications, the
comparison maps and all proofs are ours (derived): the ideal-adic variant is
Milne's definition for the reductions `F / I ^ n F` of one sheaf, and the
equivariant variant equips each `H^q(X, F_m)` with the published action of
`G` and takes the limit of representations.

## Scope

The module defines inverse limits of cohomology modules and proves their
degree-zero identifications. It does not impose Milne's condition on
`l`-adic sheaves, define `l`-adic sheaves or the lisse sheaf `W̃`, define
cohomology with compact support, `ℚ_ℓ`-coefficients or derived limits
(`lim^1`), prove that `limitComparison` is an isomorphism, injective or
surjective in positive degrees, or construct the spectral sequence (4.10.4)
or the Mittag-Leffler argument of Proposition 4.10. The degree-zero
divisible-system identification needs the explicit hypothesis `hΓ`, which is
not proved. Mathlib's `AlgebraicGeometry.Scheme.EllAdicCohomology` (pro-étale
cohomology with coefficients in continuous `ℤ_[ℓ]`-valued functions,
`Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`) is a different
construction, and no comparison with it is made. The group `G` acts on
abstract modules: there are no topologies, smoothness conditions or Galois
actions.

Source registrations: Milne 1980, `milne-1980-etale-cohomology`, SHA-256
`0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`; Harris
1999, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
