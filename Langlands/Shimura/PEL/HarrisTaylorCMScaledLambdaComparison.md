# The `λ`-adic cohomology over scaled levels compared with the fixed-level `λ`-adic cohomology

The published `cmHarrisScaledLambdaCohomology ... l degree` is a functor of the
scaled level. At a scaled level `X` with level `U` its value is
`K_λ ⊗_R lim_k H^d(X̄_U, W_k)` with an action of `Gal(F̄/F)`. The published
`cmHarrisLambdaCohomology ... U ... l degree` has the same underlying space,
built at the fixed small level `U`. The two Galois actions are defined
through different coefficient diagrams. This module proves that the actions
agree and builds the resulting isomorphisms

`ψ_X : cmHarrisScaledLambdaCohomology(X) ≅ cmHarrisLambdaCohomology(X.level)`

in `Action (ModuleCat K_λ) (Field.absoluteGaloisGroup F)`. It then computes,
for morphisms `f : X ⟶ Y` of scaled levels with the same level, the induced maps
`T(f) = ψ_Y⁻¹ ≫ F(f) ≫ ψ_X` on the fixed-level `λ`-adic cohomology, in the
form of the three hypotheses of the published descent construction
`cmScaledDescent` (module `HarrisTaylorCMScaledDescent`):

- raising the exponent from `n` to `n'` acts by `ℓ ^ (n' - n)`;
- shifting both exponents of a morphism does not change `T`;
- a self-morphism of a scaled level whose transporter lies in the level acts
  as the identity.

The declarations of the main part are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The generic helpers are in
the namespaces listed under "Generic helpers" below.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §4, printed p. 311, defines the `ℓ`-adic sheaf
`W̃ = lim ℒ̃_m ⊗_𝒪 L_ℓ` on the geometric fibre `S̄_K(N)` and its cohomology
`H^{i+j}(S̄_K(N), W̃)`. Proposition 4.10 (printed p. 311) states that, as
`K(N)^{ℓ,p}` varies, the spectral sequences are `GG(A_f^{ℓ,p})`-equivariant.
Printed pp. 312-313 use the `λ`-adic representations of `Gal(F̄/F)` on the
isotypic parts of `H^{n-1}(S̄_K(N), W̃)`. Following Milne, *Étale cohomology*,
Chapter V, §1, printed pp. 163-165, the cohomology of an `ℓ`-adic sheaf is the
limit of the torsion cohomology (p. 164), and one passes to vector spaces by
extension of scalars (pp. 164-165).

In the Library the `λ`-adic cohomology at one small level is
`cmHarrisLambdaCohomology`. Transporters act on the `λ`-adic cohomology over
the scaled levels, `cmHarrisScaledLambdaCohomology`, from the published module
`HarrisTaylorCMScaledGaloisCohomology`. The published descent module turns a
functor `G` on scaled levels, objects `O U` at the small levels,
isomorphisms `ψ X : G.obj (op X) ≅ O X.level`, and the three laws above into a
functor on small levels. This module supplies `ψ` and the laws for
`G = cmHarrisScaledLambdaCohomology` and `O = cmHarrisLambdaCohomology`. It
does not apply the descent, and it formalizes no statement of Harris. The
equivariance under transporters with nontrivial `ℓ`-component is a
construction internal to the Library and is not attributed to Harris.

## Inputs

The binders `E`, `F`, `A`, `D`, `L`, `C`, the named premises `preservation`
through `htor`, `q`, `[Module.Finite ℚ A]`, `K`, `W`, `ρ`, `p`, `existence`,
`geometry` and `hRigid` are those of the published
`HarrisTaylorCMScaledGaloisCohomology`. In particular
`hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity ... U.obj`. Below
`...` abbreviates
`D C preservation composition unitCoherence associativity comparison symmetry
stability square universality dualityNaturality polarizationStability
compatibility h htor q p ρ existence geometry hRigid`, followed by `l degree`
where the declaration takes them. `Galois = AlgebraicClosure F ≃ₐ[F]
AlgebraicClosure F`, `R = HarrisCoefficientIntegers K p`,
`ℓ = harrisCoefficientPrime p`, and `K_λ = FiniteCompletion K l.1` with the
`R`-algebra structure `harrisCoefficientComponentAlgebra K p l`. The
cohomology declarations take the instance binders of the published module: for
every small level `U`, `HasDerivedCategory.{wS}` for the module sheaves over
`R` on the geometric level `X̄_U`, and `HasDerivedCategory.{wR} (ModuleCat.{0} R)`.

Published inputs:

- `HarrisTaylorCMScaledGaloisCohomology`: the scheme diagram
  `cmScaledGeometricGaloisSchemes`, the coefficient diagram
  `cmHarrisScaledGeometricGaloisCoefficientDiagram`, the cohomology action
  diagram `cmHarrisScaledGaloisCohomologyAction`, `cmHarrisScaledLambdaCohomology`
  (`Functor.curry.obj (cmHarrisScaledGaloisCohomologyAction ...) ⋙ lim`
  followed by extension of scalars), and `baseChangeActionFunctor`.
- `HarrisTaylorCMGeometricGaloisCohomology` and `HarrisTaylorCMLambdaCohomology`:
  the fixed-level Galois action `cmHarrisGeometricGaloisCohomologyAction`, with
  `_obj_ρ` and `_map_hom`, and `cmHarrisLambdaCohomology`, the extension of
  scalars of its limit over the stages.
- `HarrisTaylorCMGeometricGaloisCoefficients`: the coefficient comparisons
  `cmGeometricGaloisInverseImageIso` for `g_σ ≫ π_U = π_U`, with
  `cmGeometricGaloisInverseImageIso_one` and
  `cmHarrisGeometricCoefficientGaloisIso_hom_app`.
- `HarrisTaylorCMLevelTransport` and `HarrisTaylorCMLevelTransportLaws`: the
  transport maps `cmHarrisTransportSheafMap`, the stage transitions
  `cmHarrisStageTransportMap`, the laws `cmHarrisTransportSheafMap_id_le`,
  `cmHarrisTransportSheafMap_raise` (`ℓ ^ (n' - n)` times the stage
  transition) and `cmHarrisTransportSheafMap_eq_of_mem`, and
  `cmSchemeTower_map_eq_id_of_mem`.
- `HarrisTaylorCMScaledLevels`: `CMScaledLevel`, `CMScaledLevel.raise` and
  `CMScaledLevel.Hom.shift`.
- `HarrisTaylorCMScaledDescent`: `cmScaledTransport`,
  `cmScaledTransport_comp`, and the hypotheses `CMScaledTransportRaise`,
  `CMScaledTransportShift` and `CMScaledTransportLevelTrivial`.
- `HarrisCoefficientPrimeValuation`: `harrisCoefficientPrime_ne_zero_completion`
  (`ℓ ≠ 0` in `K_λ`).
- Generic Library modules: `EtaleCoefficientDiagramPullback`
  (`squareInverseImageMap_base_id`, `projectionInverseImageIso_congr_top`),
  `EtaleInverseImageRestrictionCoherence` (`inverseImageIsoRestriction_congr`,
  `inverseImageIsoRestriction_id`), `EtaleDerivedSheafCoherence`
  (`cohomologyPullback_id`), `EtaleGeometricCoefficientPullback`
  (`cohomologyPullbackWithCoefficients`) and `EtaleGeometricActionDiagram`
  (`CoefficientDiagram.cohomologyAction_obj_ρ` and `_map_hom`).

## Generic helpers

- `CategoryTheory.injectiveResolutions_additive`: the functor
  `injectiveResolutions C` is additive. The descents of `f + g` and of `f` plus
  `g` lift the same morphism, so they are homotopic
  (`InjectiveResolution.descHomotopy`).
- `CategoryTheory.Functor.rightDerivedToHomotopyCategory_additive` proves
  additivity of the homotopy-category-valued construction. Additivity of
  `F.rightDerived n` reuses the existing
  `Langlands.AlgebraicGeometry.Modules.CechResolution.rightDerived_additive`
  instance from [RightDerivedAdditive](../../Cohomology/RightDerivedAdditive.md).
- `Langlands.Geometry.EtaleDerivedSections.cohomology_additive`: small étale
  cohomology `cohomology X R n` is additive.
- In `Langlands.Geometry.EtaleDerivedGlobalPullback`:
  `cohomologyPullbackWithCoefficients_congr` (for `e : f = f'`, pullback along
  `f` with coefficient map `(inverseImageCongr e).hom.app F ≫ α` is pullback
  along `f'` with `α`), `cohomologyPullbackWithCoefficients_id` (along `𝟙 X`,
  with coefficient map `(inverseImageId).hom.app F ≫ β` it is the cohomology of
  `β`), and `cohomologyPullbackWithCoefficients_nsmul` (it commutes with
  `n • ·` in the coefficient map).
- `Langlands.Geometry.EtaleInverseImage.inverseImageIsoRestriction_restrictionCongr_id`
  (with `@[reassoc]`): for an étale `φ : X ⟶ X` with `e : φ = 𝟙 X`, the
  comparison of inverse image with restriction followed by the restriction
  comparisons for `e` and for the identity is
  `(inverseImageCongr e).hom.app M ≫ (inverseImageId).hom.app M`.
- `Langlands.Shimura.LatticeGaloisRepresentation.baseChangeActionFunctor_additive`:
  extension of scalars of Galois actions is additive.
- `CategoryTheory.Limits.lim_map_nsmul_id`: `lim.map (n • 𝟙 F) = n • 𝟙 (lim.obj F)`.

## Main part

### Tower maps and coefficient transitions

- The published `cmGeometricSchemeTower_map_eq_id_of_mem` is reused: the geometric
  tower map of a
  transporter `b : U ⟶ U` whose element lies in `U` is the identity. It is the
  base change to `F̄` of `cmSchemeTower_map_eq_id_of_mem`.
- `cmScaledGaloisArrow D p ρ f κ σ` (an `abbrev`): the arrow `((f.op, κ), σ)`
  of the index category of scaled levels, stages and Galois elements.
- `cmScaledGeometricGaloisSchemes_map_sameLevel`: for `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩`
  whose geometric tower map is the identity, the scheme map of
  `((f, κ), σ)` is the Galois map `g_σ`.
- `cmHarrisScaledGeometricGaloisCoefficientDiagram_map_eq` (`rfl`): the
  transition of the scaled geometric coefficient diagram along an arrow `a`,
  unfolded as the square comparison of inverse images followed by the inverse
  image along `π` of the comparison of inverse image with restriction and the
  transport map.
- `cmHarrisScaledGeometricGaloisCoefficientDiagram_map_sameLevel`: let
  `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩` have identity tower maps, and let its transport maps
  be `c` times the stage transitions, for a natural number `c`. Then the
  transition along `((f, κ), σ)` is `c` times the identification of inverse
  images along the equal maps `g_σ ≫ T̄(f) = g_σ`, followed by the Galois
  comparison `(cmGeometricGaloisInverseImageIso U σ).hom` and the inverse image
  of the stage transition `κ`.

### Galois actions and level maps at the stages

- `cmHarrisScaledGaloisCohomologyAction_obj_ρ` and `_map_hom`: the Galois
  action at `(X, k)` and the map of an arrow of scaled levels and stages, as
  cohomological pullbacks with coefficients. They specialize the generic
  `CoefficientDiagram.cohomologyAction_obj_ρ` and `_map_hom`.
- `cmHarrisScaledGaloisCohomologyAction_obj_ρ_eq`: at every scaled level `X`,
  stage `k` and `σ`, the action of `σ` on `H^d(X̄_U, W_k)` over scaled levels
  equals the action at the level `U` from
  `cmHarrisGeometricGaloisCohomologyAction`. The equation is stated in the
  type of endomorphisms of `H^d(X̄_U, W_k)`. The proof applies the previous
  lemma to `f = 𝟙 X` and `c = 1`, using `cmHarrisTransportSheafMap_id_le`, and
  then `cohomologyPullbackWithCoefficients_congr`.
- `cmHarrisScaledGaloisCohomologyAction_map_sameLevel`: under the same
  hypotheses on `f`, the map of `(f, κ)` on the stage cohomology is
  `c • (cohomology ...).map ((cmHarrisGeometricCoefficientSystem ...).map κ)`,
  using `cmGeometricGaloisInverseImageIso_one`,
  `cohomologyPullbackWithCoefficients_nsmul` and
  `cohomologyPullbackWithCoefficients_id`.

### The identifications

- `cmHarrisScaledStageIso ... degree X k`: the isomorphism in
  `Action (ModuleCat R) Galois` from the scaled-level action at `(X, k)` to the
  fixed-level action at stage `k` of `X.level`. Its underlying map is the
  identity of `H^d(X̄_U, W_k)`. It is equivariant by `_obj_ρ_eq`.
- `cmHarrisScaledStageNatIso ... degree X`: the natural isomorphism, in the
  stage, from `(Functor.curry.obj (cmHarrisScaledGaloisCohomologyAction ...
  degree)).obj (op X)` to `cmHarrisGeometricGaloisCohomologyAction ... X.level
  ... degree`, with components `cmHarrisScaledStageIso`. Naturality is
  `_map_sameLevel` for `f = 𝟙 X`, `c = 1`, compared with
  `cmHarrisGeometricGaloisCohomologyAction_map_hom`.
- `cmHarrisScaledStageNatIso_hom_app_hom` and `_inv_app_hom` (`rfl`): the
  underlying maps of the components are identities.
- `cmHarrisScaledStageNatIso_conj_app_hom`: for `f : X ⟶ Y`, the stage-`k`
  component of `N_Y⁻¹ ≫ (curry ...).map f.op ≫ N_X` has the underlying map of
  `(f.op, 𝟙 k)`.
- `cmHarrisScaledStageNatIso_conj_sameLevel`: for `f : ⟨U, s⟩ ⟶ ⟨U, s'⟩` with
  identity tower maps and transport maps `c` times the stage transitions,
  `N_{⟨U, s'⟩}⁻¹ ≫ (curry ...).map f.op ≫ N_{⟨U, s⟩} = c • 𝟙`.
- `cmHarrisScaledLambdaComparison ... l degree X`: the isomorphism `ψ_X` from
  `(cmHarrisScaledLambdaCohomology ... l degree).obj (op X)` to
  `cmHarrisLambdaCohomology ... X.level ... l degree`. It is
  `baseChangeActionFunctor.mapIso (lim.mapIso (cmHarrisScaledStageNatIso ...
  degree X))`.
- `cmHarrisScaledLambdaCohomology_map`, `cmHarrisScaledLambdaComparison_hom`
  and `_inv` (`rfl`): the map of `f` on the scaled `λ`-adic cohomology, `ψ_X`
  and `ψ_X⁻¹` as extensions of scalars of limits.

### The transport maps and the three laws

Write `T(f) = cmScaledTransport D ρ p G O ψ f = (ψ Y).inv ≫ G.map f.op ≫
(ψ X).hom` for `G = cmHarrisScaledLambdaCohomology ... l degree`,
`O = fun U => cmHarrisLambdaCohomology ... U ... l degree` and
`ψ = cmHarrisScaledLambdaComparison ... l degree`.

- `cmScaledTransport_cmHarrisScaledLambdaComparison`: `T(f)` is
  `baseChangeActionFunctor.map (lim.map (N_Y⁻¹ ≫ (curry ...).map f.op ≫ N_X))`.
- `cmScaledTransport_cmHarrisScaledLambdaComparison_of_conj`: if
  `N_{⟨U, s'⟩}⁻¹ ≫ (curry ...).map f.op ≫ N_{⟨U, s⟩} = c • 𝟙`, then
  `T(f) = (c : K_λ) • 𝟙`. The proof uses `lim_map_nsmul_id` and the
  additivity of extension of scalars.
- `cmHarrisScaledLambdaComparison_raise ... l degree :
  CMScaledTransportRaise D ρ p K_λ G O ψ`: `T(CMScaledLevel.raise U h) =
  (ℓ : K_λ) ^ (n' - n) • 𝟙` for `h : n ≤ n'`. It follows from
  `cmHarrisTransportSheafMap_raise` and `_conj_sameLevel` with
  `c = ℓ ^ (n' - n)`.
- `cmHarrisScaledLambdaComparison_levelTrivial ... l degree :
  CMScaledTransportLevelTrivial D ρ p G O ψ`: if the transporter of
  `f : Y ⟶ Y` lies in `Y.level`, then `T(f) = 𝟙`. It follows from
  `cmSchemeTower_map_eq_id_of_mem`, `cmGeometricSchemeTower_map_eq_id_of_mem`,
  `cmHarrisTransportSheafMap_eq_of_mem` and `_conj_sameLevel` with `c = 1`.
- `cmHarrisScaledLambdaComparison_shift ... l degree :
  CMScaledTransportShift D ρ p G O ψ`: `T(CMScaledLevel.Hom.shift f k) = T(f)`.
  The proof does not use a separate law for shifts. The morphisms
  `raise ≫ shift f k` and `f ≫ raise` are equal, so by `cmScaledTransport_comp`
  and the raise law `ℓ ^ k • T(shift f k) = ℓ ^ k • T(f)`. Then `ℓ ^ k ≠ 0` in
  the field `K_λ` cancels the factor.

## Lean notes

The module sets `maxHeartbeats` to 800,000 for the whole file. It uses the
options `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false` and
`backward.defeqAttrib.useBackward true`, as the published modules it builds on
do, together with `quotPrecheck false` for its local notations and
`autoImplicit false`. The unused-variables linter is switched off for
`cmHarrisScaledGeometricGaloisCoefficientDiagram_map_eq` only: its instance
binder `hE` is used implicitly by the statement and passed by name at the call
site. The stage objects of the scaled and fixed-level actions are
definitionally equal, but checking that by unfolding is very expensive. The
equivariance proofs therefore state their equations with `@Eq` in the type of
maps of `H^d(X̄_U, W_k)` and compare Galois actions through the proved
equations above, not by `rfl`.

## Provenance

This module is a derived construction. It identifies two Library
implementations of the `λ`-adic cohomology of the geometric fibre with
coefficients in Harris's `ℓ`-adic sheaf `W̃` (Harris 1999, printed
pp. 311-313; Milne, Chapter V, §1, printed pp. 163-165): the one over scaled
levels, on which transporters act, and the one at a fixed small level. It
computes the action of the morphisms between scaled levels with the same
level. The scaled levels, the transport maps and their laws, the descent
hypotheses and both cohomology objects are the Library's. The comparison
isomorphisms and the three laws are internal to the Library. The generic
helpers use standard additivity and limit identities. Additivity of
right derived functors reuses the published `rightDerived_additive` instance;
the geometric tower identity for level elements reuses
`cmGeometricSchemeTower_map_eq_id_of_mem` from
[HarrisTaylorCMGeometricLevelCosets](HarrisTaylorCMGeometricLevelCosets.md).
The remaining helpers provide the comparisons in the forms used here.
