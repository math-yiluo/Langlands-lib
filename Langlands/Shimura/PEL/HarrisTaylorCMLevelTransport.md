# Transport data for Harris's coefficient systems along CM transporters

## Purpose and provenance

Harris (1999), *Galois properties of cohomological automorphic forms on GL(n)*,
Sections 3-4, printed pp. 306-311, attaches to `(ρ, W)` and a `K_ℓ`-stable lattice
`ℒ_W` the coefficient systems `ℒ̃_m` on the Shimura varieties, with
`ℒ_m = ℒ / ℓ^m`. The cohomology `H^d(S, W)` of the tower carries the action of
the finite-adelic group through the maps induced by inclusions and translations
of levels. This file constructs these maps on the Library's coefficient sheaves
`cmHarrisCoefficientSystem` (in
[HarrisTaylorCMCoefficientSystem](HarrisTaylorCMCoefficientSystem.md)). It
works over the CM schemes over the reflex field, `cmSchemeTower q`, and proves
their identity and composition laws. The Galois action is added later, by
pulling the resulting diagram back to the geometric fibres. The construction is
derived. It uses the generic transport maps of
[EtaleAssociatedTransport](../Coefficients/EtaleAssociatedTransport.md), the
scaled transporters and torsion maps of
[HarrisTaylorCMScaledLevels](HarrisTaylorCMScaledLevels.md), and the Library's
normal CM torsors `cmNormalGeometricTorsor_of_dominantCriterion`.

Throughout, `ℓ = harrisCoefficientPrime p` and `R = HarrisCoefficientIntegers K p`.
The coefficient level of a small level `U` at stage `k` is
`U_k = cmHarrisCoefficientLevel D ρ p U ℓ hℓ k`, the kernel of `U` acting on
`ℒ_U / ℓ^k`. The stage-`k` coefficient sheaf on the CM scheme `X_U` is the sheaf
associated with the normal torsor `X_{U_k} → X_U` (group `U / U_k`) and the module
`ℒ_U / ℓ^k` (`cmHarrisCoefficientDiagram`). The rigidity hypothesis is required at
every small level:
`hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity ... U.obj`. It is used
for the normal torsors at all levels, and for etaleness of all transporter maps
(`representedCMSchemeTower_map_etale_of_dominantCriterion`).

## Transporter bookkeeping

For a transporter `b : V ⟶ U` of small CM levels with translating element `a`
(in the opposite group):

* `smallCMTransporterConj D b : V →* U` is `v ↦ a⁻¹ v a`.
* `smallCMTransporterResidualMap D b V' U' h` is the induced map
  `V / V' →* U / U'` of residual groups, for normal `V' ≤ V` and `U' ≤ U` with
  `a⁻¹ V' a ⊆ U'`.
* `smallCMTransporterRestrict D b T U' h : T ⟶ U'` is the transporter with the
  same element, for `a⁻¹ T a ⊆ U'`.
* `cmSchemeTower_transporterRestrict_comm`: the tower map of `T ⟶ U'` followed by
  that of `U' ≤ U` equals the tower map of `T ≤ V` followed by that of `b`. Both
  are the tower map of the transporter `T ⟶ U` with element `a`.

Generic etale lemmas:

* `etaleObjectPullback_hom_ext`: two maps into a base change
  `(etaleObjectPullback φ).obj B` agree once their first projections agree. The
  second projections agree because both maps lie over the base.
* `etaleTorsorPullbackCompMap_left`, `etaleTorsorPullbackCompMap_fst_fst` and
  `etaleTorsorPullbackCompMap_fst_snd` describe the comparison of iterated base
  change (`etaleTorsorPullbackCompMap` of `EtaleAssociatedTransport`) through its
  projections, using the Library's `etaleObjectPullbackComp` lemmas.

## Transport data between normal torsors

`cmNormalTransportToSource` takes the normal torsor `X_T → X_V` of a normal level
`T ≤ V` with `a⁻¹ T a ⊆ U'`. It maps this torsor to the base change along `φ` of
the normal torsor `X_{U'} → X_U`. The map is the pullback lift of the tower maps
of `T ⟶ U'` and `T ≤ V`. Here `φ` is a scheme map with `hφ : φ = (tower).map b`;
keeping `φ` separate allows equal scheme maps that are not syntactically equal.
`cmNormalTransportToSource_fst` and `_snd` give its projections.
`cmNormalTransportToSource_comp` proves that the source maps of composable
transporters compose through `etaleTorsorPullbackCompMap`.

`cmNormalTransportDatum` is the `EtaleTransportDatum` along `φ`, from
`(X_{U'} → X_U, M)` to `(X_{V'} → X_V, M')`. Here `M` and `M'` are module
representations of `U / U'` and `V / V'`. Its fields are:

* the common cover, the normal torsor of `T`, with group `V / T`;
* the group maps `smallCMTransporterResidualMap` to `U / U'` and the quotient
  map to `V / V'`;
* the source map `cmNormalTransportToSource`, and the target map, the tower map
  of `T ≤ V'`;
* a coefficient map `c : M ⟶ M'`, satisfying
  `M(a⁻¹ v a) ≫ c = c ≫ M'(v)` for all `v ∈ V`.

The equivariance of the source map follows from two facts. First, the tower maps
of `T ⟶ U'` with elements `v⁻¹ a` and `a (a⁻¹ v a)⁻¹` coincide, since the elements
are equal. Second, deck transformations of `X_T` lie over `X_V`. The equivariance
of the target map follows from equality of transporters.

## Harris's coefficient systems

For a morphism `f : X ⟶ Y` of scaled levels (`CMScaledLevel D ρ p`) and stages
`k' ≤ k`:

* `cmScaledTransportLevel D p ρ f k' k` is the standard common level
  `{x ∈ X_{k'} : a⁻¹ x a ∈ Y_k}`. This is `smallCMHeckeLevel` of the coefficient
  levels of the levels of `X` and `Y`. It comes with membership
  (`mem_cmScaledTransportLevel`), containment and conjugation lemmas, and the
  instance `cmScaledTransportLevel_normal`. The level is normal in the level of
  `X` because `X_{k'}` and `Y_k` are normal and `a⁻¹ (level of X) a` lies in the
  level of `Y`.
* `cmHarrisTransportDatumAt` is `cmNormalTransportDatum` with `U' = Y_k`,
  `V' = X_{k'}`, `M = ℒ_Y / ℓ^k`, `M' = ℒ_X / ℓ^{k'}` (the actions of
  `cmHarrisCoefficientDiagram`) and coefficient map
  `cmHarrisTorsionTransport D ρ p f hk`. Its equivariance is
  `cmHarrisTorsionTransport_comm`. The common level `T` is any admissible level.
  `cmHarrisTransportDatum` uses the standard common level.
* `cmHarrisTransportSheafMap` is the transport map (`EtaleTransportDatum.sheafMap`)
  of the standard datum. It maps the restriction along `φ` of the stage-`k`
  coefficient sheaf of the level of `Y` to the stage-`k'` coefficient sheaf of the
  level of `X`.
* `cmHarrisTransportDatumAt_sheafMap_eq`: for admissible common levels `T₁ ≤ T₂`,
  the transport maps agree. This is `sheafMap_eq_of_refines` with the tower map
  of `T₁ ≤ T₂`.
* `cmHarrisTransportDatumAt_sheafMap_congr`: for `e : φ₁ = φ₂`, the transport map
  along `φ₁` is the identification `restrictionCongr e` followed by the transport
  map along `φ₂`.
* `cmHarrisTransportSheafMap_id`: for `𝟙 Y` and equal stages, along `φ` with
  `e : φ = 𝟙`, the transport map is `restrictionCongr e` followed by
  `restrictionId`. The proof uses `sheafMap_id` of `EtaleAssociatedTransport`.
  The source map followed by the first projection is the transporter with element
  `1`, which is the inclusion. The coefficient map is the identity transition of
  the torsion system.
* `cmScaledCompositeLevel D p ρ fb fa k'' k' k`, for `fb : X ⟶ Y` and `fa : Y ⟶ Z`,
  is the intersection of the standard common level of `fb` with
  `{x : b⁻¹ x b ∈ standard level of fa}`, where `b` is the element of `fb`. It
  comes with containment and conjugation lemmas (including
  `cmScaledCompositeLevel_le_standard`, containment in the standard level of
  `fb ≫ fa`) and normality (`cmScaledCompositeLevel_normal`).
* `cmHarrisTransportSheafMap_comp`: for `k'' ≤ k' ≤ k`, scheme maps `φa`, `φb`
  and `φab` equal to the tower maps of `fa`, `fb` and `fb ≫ fa`, and
  `e : φb ≫ φa = φab`,

  ```text
  restrictionComp(φa, φb) ≫ restrictionCongr(e) ≫ transport(fb ≫ fa)
    = restriction_φb(transport(fa)) ≫ transport(fb).
  ```

  The proof first uses the congruence lemma and the refinement lemma to replace
  the transport map of `fb ≫ fa` by that of the datum along `φb ≫ φa` with common
  level `cmScaledCompositeLevel`. It then applies `sheafMap_comp` of
  `EtaleAssociatedTransport`. The map of common covers into the base change of
  the cover of `fa` is `cmNormalTransportToSource` for `fb`. The map to the cover
  of `fb` is the tower map of the inclusion. The source-map condition is
  `cmNormalTransportToSource_comp`, and the coefficient condition is
  `cmHarrisTorsionTransport_comp`.

## The coefficient diagram

* `cmScaledLevelForget` forgets the exponent of a scaled level.
* `cmScaledSchemeDiagram : (CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ ⥤ Schemeᵒᵖ` sends
  `(X, k)` to the CM scheme of the level of `X`, and a morphism to the opposite of
  the tower map of its transporter. The stage index does not change the scheme.
* `cmScaledSchemeDiagram_etale`: every transition is etale.
* `cmHarrisScaledCoefficientDiagram` is an `EtalePullback.CoefficientDiagram` over
  `cmScaledSchemeDiagram`. Its vertex `(X, k)` is the Library's coefficient sheaf
  `(cmHarrisCoefficientSystem ... X.level ρ p ℓ hℓ existence geometry (hRigid _)).obj k`.
  Its transition for a morphism `(f, k' ≤ k)` is `cmHarrisTransportSheafMap`. Its
  identity and composition laws are `cmHarrisTransportSheafMap_id` and
  `cmHarrisTransportSheafMap_comp`, matched with `diagramRestrictionId` and
  `diagramRestrictionComp`. Restricted to the identity transporters of a level
  and varying stages, the transitions are transport maps whose coefficient maps
  are the transitions of the torsion system.

Three declarations raise the heartbeat limit to a finite value:
`cmNormalTransportToSource_comp` (1,600,000), `cmHarrisTransportSheafMap_comp` and
`cmHarrisScaledCoefficientDiagram` (3,200,000 each).

## Scope

The file constructs no cohomology and no Galois action. It does not prove that the
transitions along pure stage changes agree with the transitions of
`cmHarrisCoefficientSystem`. Passing to geometric fibres, cohomology, the `ℓ`-adic
limit, inverting `ℓ`, the normalization by powers of `ℓ` and the functor on small
levels are separate constructions.
