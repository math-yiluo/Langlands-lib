# Canonical cohomology pullback computed on arbitrary right resolutions

Module `Langlands.AlgebraicGeometry.Modules.CohomologyPullbackResolution`.

## Purpose

For a morphism `h : Y ⟶ X` of schemes over `Spec R`, the Library defines the
canonical pushforward comparison `canonicalPushforwardCohomologyMap h N n :
H^n(X, h_* N) ⟶ H^n(Y, N)` and the canonical cohomology pullback
`relativeCohomologyPullback h M n : H^n(X, M) ⟶ H^n(Y, h^* M)`. Both are defined
with derived categories and Mathlib's chosen injective resolutions. Here
`H^n(X, -)` is `relativeCohomology X.hom n`, the right derived functors of
`relativeGlobalSections X.hom`. This module proves that both maps can be
computed on *arbitrary* right resolutions, for example Čech resolutions. The
resolutions need not be acyclic.

Every right resolution `ε : M[0] ⟶ K` (a quasi-isomorphism of `ℕ`-indexed
cochain complexes) comes with the Library's comparison map
`resolutionComparison F ε n : H^n(F K) ⟶ (R^n F) M`. The main theorem says that
these comparison maps carry the map of section complexes induced by a
compatible map of resolutions to the canonical maps.

## Main results

Namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`. Throughout,
`R : CommRingCat`, `X Y : Over (Spec R)`, `h : Y ⟶ X`, and `h_*` is
`Scheme.Modules.pushforward h.left`.

- `resolutionComparison_comp_canonicalPushforwardCohomologyMap`. Fix modules
  `M` on `X` and `N` on `Y`, and a map `a : M ⟶ h_* N`. Fix right resolutions
  `εX : M[0] ⟶ KX` and `εY : N[0] ⟶ KY` (both with `[QuasiIso]`), and a map
  `ψ : KX ⟶ h_* KY` of `ℕ`-indexed complexes on `X`. Assume `ψ` is compatible
  with the augmentations over `a`, that is,
  `εX ≫ ψ = single₀.map a ≫ mapResolutionAugmentation h_* εY`. Then for every
  `n : ℕ`,

  `resolutionComparison Γ_X εX n ≫ H^n(X, a) ≫ canonicalPushforwardCohomologyMap h N n`
  `= homologyMap (Γ_X(ψ) ≫ S) n ≫ resolutionComparison Γ_Y εY n`.

  Here `Γ_X = relativeGlobalSections X.hom` and `Γ_Y = relativeGlobalSections Y.hom`.
  `S : Γ_X(h_* KY) ≅ Γ_Y(KY)` is the termwise isomorphism
  `(Functor.mapHomologicalComplexCompIso (relativePushforwardSectionsIso h) _).app KY`,
  built from the Library's identification `Γ_X ∘ h_* ≅ Γ_Y`.
- `resolutionComparison_comp_relativeCohomologyPullback`. This is the case
  `N = h^* M` with `a` the unit of the pullback–pushforward adjunction. With
  `εY : (h^* M)[0] ⟶ KY` and `ψ` compatible over the unit, it gives
  `resolutionComparison Γ_X εX n ≫ relativeCohomologyPullback h M n =
  homologyMap (Γ_X(ψ) ≫ S) n ≫ resolutionComparison Γ_Y εY n`.
- `resolutionComparison_comp_relativeCohomologyPullback_coefficient`. This is
  the same statement followed by a coefficient map `b : h^* M ⟶ N`, with `ψ`
  compatible over the adjoint `homEquiv b : M ⟶ h_* N`. Its left side is
  `resolutionComparison Γ_X εX n ≫ relativeCohomologyPullback h M n ≫ H^n(Y, b)`.
- `derivedResolutionComparison_comp_pushforwardSingle` states the main theorem
  before taking cohomology, in the unbounded derived category of `R`-modules.
  The canonical derived comparison of `εX`, followed by `Plus.ι` of the derived
  map of `a` and `(pushforwardSingleDerivedSectionsComparison h).app N`, equals
  `Q` of the extended section-complex map, followed by the canonical derived
  comparison of `εY`.
- `mapExtendIso_hom_comp_sectionsMap` shows that the bounded below section map
  used there is the extension by zero of `Γ_X(ψ) ≫ S`.

## General helpers

Namespace `Langlands.Cohomology.AcyclicResolution`. Each is stated for abelian
categories.

- `natPlus K` is a `ℕ`-indexed complex extended by zero to a bounded below
  `ℤ`-indexed complex (`CochainComplex.Plus`). `natPlusMap` is the same for
  maps.
- `natPlusAugmentation ε : (singlePlusFunctor C).obj A ⟶ natPlus K` is the
  extended augmentation. It is a quasi-isomorphism after localization
  (instance `isIso_Q_map_natPlusAugmentation`).
- `natPlusAugmentation_comp_natPlusMap`: for an injective resolution `I`, a
  lift `φ` compatible with the augmentations extends to
  `DerivedPlus.resolutionPlusι I`.
- `natPlusMapTo P ψ : natPlus KX ⟶ P.mapCochainComplexPlus.obj (natPlus KY)`
  is the extension of `ψ : KX ⟶ P(KY)`, composed with `DerivedPlus.mapExtendIso`.
  `natPlusAugmentation_comp_natPlusMapTo` turns compatibility of `ψ` over `a`
  into compatibility of the extended maps:
  `natPlusAugmentation εX ≫ natPlusMapTo P ψ = singlePlus(a) ≫
  (singlePlusMapIso P).hom.app N ≫ P⁺(natPlusAugmentation εY)`.
- `extendXMapIso_compIso` and `mapExtendIso_compIso`: extension by zero
  commutes with the comparison isomorphism of a composite functor
  `F ⋙ G ≅ H`.
- `derivedResolutionComparison_eq_unit` writes the canonical derived comparison
  `derivedResolutionComparison F ε` through the unit of the bounded below right
  derived functor. It equals
  `(QCompιIso).inv ≫ Plus.ι.map (unit.app (natPlus K) ≫
  RF⁺.map (inv (Q.map (natPlusAugmentation ε)) ≫ (singlePlusQIso C).inv.app A))`.
- `derivedResolutionHomologyIso_hom_naturality_of_extend`: a map of `ℤ`-indexed
  image complexes that is the extension of a map `u` of `ℕ`-indexed image
  complexes induces `homologyMap u n` under `derivedResolutionHomologyIso`.

## Proof

1. *Lemma U* (`derivedResolutionComparison_eq_unit`). The canonical comparison
   is computed with the lift `φ = lift ε (𝟙 A)` into Mathlib's injective
   resolution `I`. Unfold `derivedResolutionIso` and `derivedComplexIso` into
   the unit and `singleIsoOfResolution`. Then use naturality of `QCompιIso.inv`
   and of the unit at `natPlusMap φ`. Finally use
   `singleIsoOfResolution_hom_eq` and `natPlusAugmentation ε ≫ natPlusMap φ =
   resolutionPlusι I`.
2. *Derived identity* (`derivedResolutionComparison_comp_pushforwardSingle`).
   Rewrite both canonical comparisons with Lemma U and move `QCompιIso.inv`
   across by naturality. This reduces the claim to an identity in the bounded
   below derived category. Unfold `pushforwardSingleDerivedSectionsComparison`
   into its four whiskered factors. Then use, in turn:
   - naturality of `singlePlusQIso` at `a`;
   - the extended compatibility `natPlusAugmentation_comp_natPlusMapTo`;
   - naturality of the Library's comparison
     `pushforwardDerivedSectionsComparison h` at `natPlusAugmentation εY`;
   - naturality of the unit at `natPlusMapTo P ψ`;
   - the factorization `pushforwardDerivedSectionsComparison_fac`.
3. *Cohomology* (`resolutionComparison_comp_canonicalPushforwardCohomologyMap`).
   Cancel the source identification `derivedResolutionHomologyIso`. Then use
   `derivedResolutionComparison_homology` for `εX` and `εY`, and
   `DerivedPlus.homologyIso_hom_naturality` for `a` (which identifies
   `H^n(X, a)` with the derived map), the cohomology of the derived identity,
   and `derivedResolutionHomologyIso_hom_naturality_of_extend`. The last of
   these takes the compatibility `mapExtendIso_hom_comp_sectionsMap`, which
   is proved from `mapExtendIso_compIso` and `extendMapIso_hom_naturality`.
4. The pullback corollaries rewrite `relativeCohomologyPullback` with the
   Library lemmas `relativeCohomologyPullback_eq_unit_pushforward` and
   `relativeCohomologyPullback_coefficient`, then apply step 3.

## Provenance

This module is derived infrastructure; it formalizes no new literature
statement. Its content is the standard homological-algebra fact that comparison
maps from arbitrary right resolutions to derived functors are natural in maps of
resolutions. No acyclicity is needed, because the statement concerns the
canonical comparison maps and not isomorphisms. The proof uses only Mathlib's bounded below derived functors and these
published Library declarations: `derivedResolutionComparison`,
`resolutionComparison`, `pushforwardSingleDerivedSectionsComparison`,
`pushforwardDerivedSectionsComparison_fac`,
`canonicalPushforwardCohomologyMap`, and the two pullback factorization lemmas.
