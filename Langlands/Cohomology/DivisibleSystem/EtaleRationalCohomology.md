# Rational `ℓ`-adic étale cohomology by extension of scalars

Author: Worker 61. Built on the published module
`Langlands.Cohomology.DivisibleSystem.EtaleAdicCohomology` of Worker 61
(`adicCohomology`, `adicSections`, `adicCohomologyZeroIso`,
`limitComparison` with its degree-zero `IsIso` instance,
`idealAdicCohomology`, `idealAdicCohomologyZeroIso`,
`equivariantAdicCohomology`, `equivariantAdicCohomologyForgetIso`,
`equivariantAdicSections`, `equivariantAdicCohomologyZeroIso`,
`harrisEtaleAdicCohomology`, `harrisEtaleAdicCohomologyZeroIso`,
`harrisEtaleAdicCohomologyZeroLimitIso`,
`harrisEtaleAdicCohomologyZeroDivisibleIso`). Through its imports it uses
Worker 13's `EtaleDerivedSections` (`ModuleSheaf`, `sections`,
`cohomology`), `EtaleAdicSystem.functor`,
`EtaleAdicSystem.equivariantFunctor` and `equivariantFunctorForgetIso`,
`EtaleCohomologyAction.EquivariantSheaf`,
`TranslationAction.Equivariant.forget`, `harrisEtaleCoefficientSystem` and
`harrisEtaleSectionsSystem`; Worker 61's `harrisEtaleDivisibleSystem` and
`harrisEtaleSectionsDivisibleSystem`
(`Langlands.Cohomology.DivisibleSystem.HarrisEtale`); and Worker 57's
`HarrisCoefficientIntegers`, `harrisCoefficientIntegersMap` and the
algebra structure `harrisCoefficientIntegersAlgebra`
(`Langlands.Shimura.Coefficients.HarrisLattice`). From Mathlib it uses
`ModuleCat.extendScalars`, `ModuleCat.restrictScalars`,
`ModuleCat.extendRestrictScalarsAdj`, `Functor.mapAction`,
`Action.forget`, `Functor.whiskerLeft`, `Functor.whiskerRight`,
`Functor.isoWhiskerLeft`, `Functor.isoWhiskerRight`,
`Functor.isIso_whiskerRight` and `Functor.associator`.

Everything is in the namespace `Langlands.Cohomology.EtaleAdicCohomology`.
Composition `f ≫ g` is `f` followed by `g`.

## Conventions

`X : Scheme.{u}` is a scheme, `R : Type u` and `S : Type u` are commutative
rings, and `S` is an `R`-algebra. As in the published `EtaleAdicCohomology`,
a sheaf is an étale sheaf of `R`-modules on `X`, `Γ(X, -)` and `H^q(X, -)`
are Worker 13's global sections and their right derived functors, and an
inverse system is a functor `F : ℕᵒᵖ ⥤ Sheaf` with objects `F_m`.
Extension of scalars is Mathlib's
`ModuleCat.extendScalars (algebraMap R S)`, which sends an `R`-module `M`
to `S ⊗_R M` (tensor product over `R`, with `S` an `R`-module through
`algebraMap R S`), with its `S`-action on the first factor. Harris writes the
tensor factor on the right (`M ⊗_𝒪 L_ℓ`) and SGA 4½ writes `M ⊗_{ℤ_ℓ} ℚ_ℓ`;
for commutative rings the two orders give isomorphic modules, but no such
isomorphism is formalized here, and the module only uses `S ⊗_R M`.

## Extension of scalars of inverse limits

- `rationalAdicCohomology X R S q`: the functor sending an inverse system
  `F` to `S ⊗_R lim_m H^q(X, F_m)`, that is, the published
  `adicCohomology X R q` followed by extension of scalars
  (`rationalAdicCohomology_obj`, by definition).
- `rationalAdicSections X R S`: `F ↦ S ⊗_R lim_m Γ(X, F_m)`, the published
  `adicSections X R` followed by extension of scalars.
  `rationalAdicCohomologyZeroIso X R S`: in degree zero,
  `rationalAdicCohomology X R S 0 ≅ rationalAdicSections X R S`, naturally
  in `F`: extension of scalars applied to the published
  `adicCohomologyZeroIso X R`.
- `rationalLimitComparison X R S q`: the natural map
  `S ⊗_R H^q(X, lim_m F_m) ⟶ S ⊗_R lim_m H^q(X, F_m)`, extension of scalars
  applied to the published `limitComparison X R q`. It is an isomorphism for
  `q = 0` (instance): the published `limitComparison X R 0` is an isomorphism,
  and whiskering an isomorphism by a functor gives an isomorphism.
- `rationalAdicCohomologyUnit X R S q`: the natural map
  `lim_m H^q(X, F_m) ⟶ S ⊗_R lim_m H^q(X, F_m)` of `R`-modules (the target
  with its `S`-action restricted to `R`), the unit of Mathlib's adjunction
  `extendRestrictScalarsAdj` between extension and restriction of scalars
  at `adicCohomology X R q`. `rationalAdicCohomologyUnit_app_apply`: it sends
  `x` to `1 ⊗ x` (by definition).

## Ideal-adic reductions

`I` is an ideal of `R` and the published `EtaleAdicSystem.functor X I`
sends a sheaf `F` to the inverse system `n ↦ F / I ^ n F`.

- `rationalIdealAdicCohomology S I q`: the functor
  `F ↦ S ⊗_R lim_n H^q(X, F / I ^ n F)`, the published
  `idealAdicCohomology I q` followed by extension of scalars.
  `rationalIdealAdicCohomology_eq`: it is the system of reductions followed
  by `rationalAdicCohomology X R S q` (by definition).
- `rationalIdealAdicCohomologyZeroIso S I`: in degree zero,
  `S ⊗_R lim_n H^0(X, F / I ^ n F) ≅ S ⊗_R Γ(X, lim_n F / I ^ n F)`,
  naturally in `F`: extension of scalars applied to the published
  `idealAdicCohomologyZeroIso I`.

## Equivariant coefficients

`G` is a group and `ρ : G →* (Aut X)ᵐᵒᵖ` an action of `G` on `X`. The
published `equivariantAdicCohomology R ρ q` sends an inverse system of
`ρ`-equivariant sheaves to `lim_m H^q(X, F_m)` as an object of
`Action (ModuleCat R) G`. Mathlib's `Functor.mapAction G` applies a functor
`ModuleCat R ⥤ ModuleCat S` to a representation of `G`, letting `g` act by
the image of its action map.

- `equivariantRationalAdicCohomology R S ρ q`: the representation of `G` on
  `S ⊗_R lim_m H^q(X, F_m)` in which `g` acts by `1 ⊗ g`, the published
  `equivariantAdicCohomology R ρ q` followed by `mapAction` of extension of
  scalars.
- `equivariantRationalAdicCohomologyForgetIso R S ρ q`: the underlying
  `S`-module of `equivariantRationalAdicCohomology R S ρ q` of `F` is
  `rationalAdicCohomology X R S q` of the underlying inverse system of
  sheaves, naturally in `F`. Forgetting the action after `mapAction` is, by
  definition, forgetting it before, and the rest is extension of scalars
  applied to the published `equivariantAdicCohomologyForgetIso R ρ q`.
- `equivariantRationalAdicSections R S ρ`: `S ⊗_R lim_m Γ(X, F_m)` as a
  representation of `G`, from the published `equivariantAdicSections R ρ`.
  `equivariantRationalAdicCohomologyZeroIso R S ρ`: in degree zero,
  `equivariantRationalAdicCohomology R S ρ 0 ≅
  equivariantRationalAdicSections R S ρ`, the image of the published
  `equivariantAdicCohomologyZeroIso R ρ`.
- `equivariantRationalAdicCohomologyUnit R S ρ q`: the `G`-equivariant map
  `x ↦ 1 ⊗ x` from `equivariantAdicCohomology R ρ q` to the restriction of
  scalars of `equivariantRationalAdicCohomology R S ρ q`, natural in `F`.
  Each component is the unit of `extendRestrictScalarsAdj`; it commutes with
  the action of `g` and with maps of inverse systems by naturality of that
  unit. `equivariantRationalAdicCohomologyUnit_app_hom_apply`: its underlying
  map sends `x` to `1 ⊗ x` (by definition).
- `equivariantRationalIdealAdicCohomology S ρ I q`: for a `ρ`-equivariant
  sheaf `F`, `S ⊗_R lim_n H^q(X, F / I ^ n F)` as a representation of `G`,
  using the published equivariant reductions
  `EtaleAdicSystem.equivariantFunctor I ρ`.
  `equivariantRationalIdealAdicCohomologyForgetIso S ρ I q`: its underlying
  module is `rationalIdealAdicCohomology S I q` of the underlying sheaf,
  naturally in `F` (from `equivariantRationalAdicCohomologyForgetIso` and
  the published `equivariantFunctorForgetIso`).

## Harris's coefficient sheaf `W̃`

The variables are those of the published `harrisEtaleAdicCohomology`: `ℓ` a
natural number, `A` a finite-dimensional `ℚ`-algebra with involution `σ`,
`L` a number field, `W` a finite-dimensional `L`-module with an algebraic
representation `ρ` of `σ.baseChange L`, `p` a finite place of `ℚ`, `U` a
compact open level, `X` a scheme, `Y` an equivariant diagram of torsors for
`harrisCongruenceGroups ρ p U ℓ` and `hY` the finite geometric torsor
hypothesis; `𝓛̃_m` are the objects of the published
`harrisEtaleCoefficientSystem ρ p U ℓ X Y hY`. Write
`𝒪 = HarrisCoefficientIntegers L p`, the product of the valuation rings of
the completions of `L` at the places above `p`, and `L_p = L ⊗_ℚ ℚ_p`
(`L ⊗[ℚ] FiniteCompletion ℚ p`). Worker 57's `harrisCoefficientIntegersMap`
is the canonical injective ring map `𝒪 ⟶ L_p`, and
`harrisCoefficientIntegersAlgebra` is the corresponding algebra structure;
these are Harris's `𝒪` and `L_ℓ` for the rational place `p`.

- `harrisEtaleRationalCohomology ℓ ρ p U X Y hY q`: the `L_p`-module
  `L_p ⊗_𝒪 lim_m H^q(X, 𝓛̃_m)`, the value of `rationalAdicCohomology` at
  `harrisEtaleCoefficientSystem`.
  `harrisEtaleRationalCohomology_eq`: it is extension of scalars along
  `harrisCoefficientIntegersMap` of the published
  `harrisEtaleAdicCohomology ℓ ρ p U X Y hY q` (by definition).
- `harrisEtaleRationalCohomologyUnit`: the `𝒪`-linear map `x ↦ 1 ⊗ x` from
  `harrisEtaleAdicCohomology` to the restriction of scalars of
  `harrisEtaleRationalCohomology`, the component of
  `rationalAdicCohomologyUnit`.
- `harrisEtaleRationalCohomologyZeroIso`: in degree zero,
  `harrisEtaleRationalCohomology … 0 ≅ L_p ⊗_𝒪 lim_m Γ(X, 𝓛̃_m)`, the limit
  of the published `harrisEtaleSectionsSystem`; extension of scalars applied
  to the published `harrisEtaleAdicCohomologyZeroIso`.
- `harrisEtaleRationalCohomologyZeroLimitIso`: in degree zero,
  `harrisEtaleRationalCohomology … 0 ≅ L_p ⊗_𝒪 Γ(X, lim_m 𝓛̃_m)`, from the
  published `harrisEtaleAdicCohomologyZeroLimitIso`.
- `harrisEtaleRationalCohomologyZeroDivisibleIso`, for `[NeZero ℓ]` and the
  hypothesis `hΓ` of the published `harrisEtaleSectionsDivisibleSystem`
  (global sections of every map `j` of `harrisEtaleDivisibleSystem` are
  epimorphisms): `harrisEtaleRationalCohomology … 0` is `L_p ⊗_𝒪` the
  inverse limit of the `ℓ`-divisible system
  `harrisEtaleSectionsDivisibleSystem`, from the published
  `harrisEtaleAdicCohomologyZeroDivisibleIso`. The hypothesis `hΓ` is not
  proved here.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §4 (Worker 61 read the rendered scanned
pages):

- printed p.311 (one-based PDF page 13): "let `𝓛_m = 𝓛 ⊗_𝒪 𝒪_m` for any
  `m`. Then `𝓛_m` forms an inverse system of `𝒪`-modules, and the inverse
  system `{𝓛̃_m}` defines a lisse `ℓ`-adic sheaf `W̃ = lim 𝓛̃_m ⊗_𝒪 L_ℓ` on
  `S̄_{K(N)}`."
- printed p.311 (one-based PDF page 13): "Proposition 4.10. There is a
  spectral sequence of `𝒪`-modules (4.10.1)
  `E_2^{i,j} = Ext^i(H_c^{2(n−1)−j}(M̆_N, L_ℓ(n − 1)), 𝒜_ℓ(GJ, ρ, H)) ⇒
  H^{i+j}(S̄_{K(N)}, W̃)`." At the end of its proof (printed p.312,
  one-based PDF page 14) Harris records the integral version (4.10.4) with
  abutment `H^{i+j}(S̄_{K(N)}, 𝓛̃)`, modelled by the published
  `harrisEtaleAdicCohomology`.

Harris does not define `H^q(S̄_{K(N)}, W̃)` on these pages. We read it
with the standard recipe for cohomology of `ℓ`-adic sheaves with rational
coefficients, recorded by Deligne, *Cohomologie étale* (SGA 4½), Lecture
Notes in Mathematics 569 (1977), *Rapport sur la formule des traces*, §2
(Worker 61 read the rendered scanned pages):

- printed p.84 (one-based PDF page 89), 2.10: "Soient `X` un schéma séparé
  de type fini sur un corps algébriquement clos `k` et `𝔉` un
  `ℚ_ℓ`-faisceau constructible sur `X`. Soit `𝔉'` un `ℤ_ℓ`-faisceau
  constructible tel que `𝔉 ∼ 𝔉' ⊗ ℚ_ℓ`. Nous verrons en (4.11) que
  `(lim H^q_c(X, 𝔉' ⊗ ℤ/ℓ^n)) ⊗_{ℤ_ℓ} ℚ_ℓ` est un `ℚ_ℓ`-espace vectoriel
  de dimension finie. Il ne dépend que de `𝔉`, et se note `H^q_c(X, 𝔉)`."
- printed p.85 (one-based PDF page 90), 2.11: `E_λ`-sheaves, for `E_λ` a
  finite extension of `ℚ_ℓ`, "sont définis comme l'ont été les
  `ℚ_ℓ`-faisceaux, avec `ℚ_ℓ` remplacé par `E_λ`, `ℤ_ℓ` par l'anneau `𝒪_λ`
  de la valuation `λ` et `ℤ/ℓ^n` par `𝒪_λ/π^n`".

SGA 4½ defines cohomology with compact support; it is cited only as the
model of the recipe "inverse limit of the torsion cohomology, then
extension of scalars to the field", which this module applies to ordinary
cohomology. In the published `HarrisLattice`, `𝒪` is the product of the
valuation rings at the places of `L` above the rational place, and the
published `harrisCoefficientRingEquiv` (`HarrisSplitting`) splits `L_ℓ = L ⊗_ℚ ℚ_ℓ` as the
product of the corresponding completions; so the coefficients are products
of the `𝒪_λ` and `E_λ` of 2.11, one factor per place (this remark is ours and
is not used in the Lean code).
`harrisEtaleRationalCohomology` is therefore our reading of Harris's
`H^q(S̄_{K(N)}, W̃)` for the published model `harrisEtaleCoefficientSystem`
of `{𝓛̃_m}`, with the qualifications of the published
`HarrisEtaleCoefficients`, `HarrisEtale` and `EtaleAdicCohomology`: `X`,
`Y` and `hY` are inputs not identified with `S̄_{K(N)}` and its covers of
level `K(N, m)`, and `ℓ` (the base of the reductions `𝓛 / ℓ ^ m`) and `p`
(the rational place of the coefficients, Harris's `ℓ` in `L_ℓ`) are
unrelated inputs, whereas Harris uses the single prime `ℓ` for both.

The general functors `rationalAdicCohomology`, `rationalAdicSections`,
`rationalIdealAdicCohomology`, the equivariant variants, the comparison and
unit maps, the degree-zero identifications and all proofs are ours
(derived): each is extension of scalars applied to the corresponding
published construction of `EtaleAdicCohomology`.

## Scope

The module defines the rational modules by extension of scalars and proves
only identifications that are images of published ones. It does not define
the lisse sheaf `W̃` or a category of `ℚ_ℓ`-sheaves, cohomology with
compact support, or Harris's spectral sequence. It does not prove
finiteness of `harrisEtaleRationalCohomology`, its independence of the
choice of lattice, that torsion in `lim_m H^q(X, 𝓛̃_m)` dies after extension
of scalars, injectivity of the unit maps, or anything about
`rationalLimitComparison` in positive degrees. The group `G` acts on
abstract modules: there are no topologies, Hecke operators, actions of
Harris's adelic groups or Galois actions.

Source registrations: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
SGA 4½, `deligne-1977-sga4-half-cohomologie-etale`, SHA-256
`fb2939521f4c0ea0cdd55a90bec2e618e32fb433c78b194e705c6d989f4e42a6`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
