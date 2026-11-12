# Apartment conjugacy fixing the intersection

The theorem
`Langlands.Geometry.Building.apartmentConjugacyFixingIntersection` has type
`ApartmentConjugacyFixingIntersectionStatement.{u}` at arbitrary universe `u`.
It proves KP Proposition 4.2.24 for the existing quotient building of supplied
`ParahoricBuildingData`, under exactly the seven hypotheses of the published
statement. It produces an element of `P.zeroSubgroup` carrying either given
apartment onto the other and fixing their intersection pointwise, including
when that intersection is empty. The statement pair and its imports are
unchanged. No availability or comparison axiom is assumed.

## Sources and provenance

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
Proposition 4.2.24, printed pp.176–177 / PDF pp.207–208. The Section 4.2
assumptions are interpreted using the authors' corrections of 1 November 2024,
registered as `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.28–29. Those corrections add Axiom 4.1.6 and correct the metric proof's
apartment-transport inputs. They leave Proposition 4.2.24 unchanged.

The implementation follows the source's convex-intersection and facet-fixer
strategy. Its maximal-common-kernel argument is an internal finite-dimensional
replacement for choosing a facet of maximal dimension. All four helper theorems
are private proof lemmas in the same module. They add no premise to the final
statement.

## Implemented proof

`exists_maximal_facet_zero` considers a nonempty segment-convex set `C` in a
finite-dimensional real affine space with a locally finite reflection
arrangement `Ψ`. For each `x`, let `D(x)` be the intersection of the linear
kernels of the roots vanishing at `x`. Choose `x` in `C` maximizing
`finrank ℝ D(x)`; the possible ranks form a nonempty finite set bounded by the
translation-space dimension. For any `y` in `C`, the Library theorem
`AffineRootSystem.GalleryGeometry.eventually_sign_smul_vadd` supplies a short
positive segment parameter preserving every nonzero root sign at `x`. At the
resulting point `z` in `C`, a vanishing root must vanish at both `x` and `y`.
Thus `D(x) ≤ D(z)`, and maximality and
`Submodule.eq_of_le_of_finrank_le` give equality. Since `y -ᵥ x` belongs to
`D(z)`, every root vanishing at `x` vanishes at `y`.

`exists_facet_fixer_controls_convex` then shows that any affine automorphism
fixing the facet of this `x` pointwise fixes `C`. For any `y` in `C`, a short
positive point of the segment from `x` to `y` lies in the facet: zero roots stay
zero by the previous lemma and nonzero signs persist by local finiteness.
Affine linearity, fixation of `x`, and cancellation of the nonzero scalar show
that the automorphism fixes `y`.

For convexity, the final proof uses the explicit metric construction from
`MetricRealizationProof`. It combines `buildingDist_smul`,
`buildingDist_apartmentMap`, `buildingDist_translatedApartmentMap` and
`exists_apartmentRetraction` into an `IsRetractionBuildingDistance` witness.
Its `isRetractionGluedDistance` and `isNonpositivelyCurved` results equip the
existing quotient with an NPC metric in which all translated apartment charts
are isometries. The private lemma `lineMap_mem_range_of_isometries` compares
the straight segments in two charts having common endpoints. Their two
endpoint distances agree and add to the endpoint distance.
`Metric.KP.eq_of_dist_eq_of_dist_add_eq` identifies their points, proving that
the preimage of the common apartment intersection is segment-convex. This
argument needs neither closedness nor completeness.

The private `ParahoricBuildingData.exists_zero_smul_base_fixing_intersection`
first treats an apartment `Y` and the base apartment. In the nonempty case,
choose `x` as above and apply `exists_zero_forall_mem_facet_smul_eq` to obtain
`r ∈ P.zeroSubgroup` carrying `Y` onto the base apartment and fixing the facet
of `x` pointwise. For any common point `y`, AS 6, via
`HasCompatibleApartmentFacets.subset_of_inter_nonempty`, places both facets
of `x` and `y` in both apartments.
`IsBuildingTitsSystem.exists_twoFacet_smul_apartment_eq` gives a second
transporter `k` stabilizing both facets. The Library's
`facetZeroStabilizer_smul_eq` shows that `k` fixes both facets pointwise.
Consequently `m = r * k⁻¹` stabilizes the base apartment and fixes the facet
of `x`. The normalizer-apartment-stabilizer axiom identifies `m` with an
affine normalizer action; `normalizer_smul_apartmentMap` and AS 6 injectivity
transfer its fixation to affine coordinates. The convex-set helper forces
`m` to fix `y`. Since `k` also fixes `y`, so does `r`. If the intersection
is empty, `exists_zero_smul_apartmentImage` supplies a transporter and the
fixation clause is vacuous.

Finally choose `t ∈ P.zeroSubgroup` with `t • A₁` equal to the base apartment,
apply the base result to `t • A₂`, and take `t⁻¹ * r⁻¹ * t`. Subgroup closure
gives its membership, the apartment equalities give its transport property,
and fixation of the translated intersection gives pointwise fixation of
`A₁ ∩ A₂`. A chamber for the Tits-system witness is obtained using
`exists_regularPoint_closure` for the supplied affine-root arrangement and
the given `HasTitsSystem` predicate.
