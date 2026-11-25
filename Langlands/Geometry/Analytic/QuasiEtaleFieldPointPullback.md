# Full field-point preservation of quasi-étale pullbacks

`localizedQuasiEtaleFieldPointPullback` proves the Library proposition
`LocalizedQuasiEtaleFieldPointPullbackStatement.{u, v, uL} K L`.
Here `K : Type u` is complete and ultrametric and `L : Type uL` is complete,
ultrametric and algebraically closed with `NormedAlgebra K L`. For any actual
pullback in `LocalizedCategory.{u, v, v}` with a quasi-étale first cospan leg,
its image under `localizedFieldPointFunctor L` is a pullback in types. The
compatibility and uniqueness are for full field points (including chart
evaluations), not only for their underlying points. No Hausdorffness assumption
on the spaces is needed.

## Implemented proof

1. **Domain restrictions.** The full point map of a canonical analytic domain
   inclusion is injective (`localizedFieldPoint_map_domainι_injective`, by
   `fieldPoint_map_originalDomainInclusion_injective` on a saturated
   presentation). For `f : X ⟶ Y` and a domain `D` of `Y`, a field point of
   `X` compatible with one of `D` has its underlying point in the literal inverse
   image of `D`, by naturality of the projection to ordinary points. Restrict
   it there using `exists_fieldPoint_lift_domainι`. The full image in `D` is
   the prescribed field point because the map to `Y` agrees and is injective
   on points of `D`. Injectivity on points of the inverse-image domain gives
   uniqueness. This proves `isPullback_fieldPoint_domainPreimage`.
2. **A domain of an étale space.** For a factorization of `f : A ⟶ X` as
   `A ≅ D ↪ W ⟶ X` with the last map étale, first take the analytic
   pullback of `W ⟶ X` against the other cospan leg. The published
   `localizedEtaleFieldPointPullback` gives its field-point pullback square.
   Restrict the first projection to the inverse image of `D`, and paste the
   field-point square from step 1 with the étale one. The analytic square from
   `isPullback_domainPreimage_comp` identifies the constructed apex with the
   apex of any given pullback of the cospan, after the isomorphism `A ≅ D`.
   Transport the field-point square along the induced isomorphisms. This proves
   `fieldPoint_isPullback_of_domainEtale`.
3. **A cover by such domains.** Given a compatible pair of field points of
   `A` and `B`, choose a domain `D` of `A` containing the underlying point of
   the first point on which the restriction of `f` has a domain–étale
   factorization. The point restricts to `D`. Now apply step 2 to the analytic
   square formed by restricting the original pullback to the inverse image
   of `D` under its first projection. The lift there maps to a full field
   point of the original apex with the prescribed images. For uniqueness, two
   lifts with the same projections both restrict to points of this same
   inverse-image domain, with the same first projection in `D` (use step 1
   with the chosen restriction) and the same second projection in `B`. Step 2
   identifies the restrictions, hence the original lifts. The functor sends
   the analytic commutativity relation to commutativity of the point maps;
   together with existence and uniqueness this gives the pullback of types
   by `Types.isPullback_iff`.
4. **Quasi-étale maps.** By definition `quasiEtale f` supplies an arrow
   isomorphism to the image of a strong quasi-étale map. Transport the input
   square to that representative. `IsQuasiEtale.exists_local_domainEtale_charts`
   gives, at each point of its source, a union of charts forming a neighbourhood.
   One member contains the point and its domain retains its étale envelope.
   These domains meet step 3's pointwise covering requirement. Transport the
   resulting pullback of full field points back along the functor images of
   the isomorphisms.

## Provenance

This is a derived field-point compatibility result for the quasi-étale site.
The local description is from Berkovich, *Vanishing cycles for formal schemes*
(1994), §3, printed pp. 543–544. The Lean proof uses the published étale
field-point pullback theorem and the actual inverse-image domain construction,
not composition, base-change stability, or right cancellation of quasi-étale
morphisms. The latter three results are separate prerequisites in the reduction
of `QuasiEtaleSite.GeometricPointStatement`.
