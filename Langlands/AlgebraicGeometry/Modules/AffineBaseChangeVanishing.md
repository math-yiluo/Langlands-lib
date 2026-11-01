# Affine base change of acyclic smooth proper line bundles

This module supplies four derived lemmas used to prove vanishing after an
arbitrary affine base change. Schemes and rings are in an arbitrary common
universe. All degree quantifiers are natural and include zero. The coefficient
is an actual line bundle, and cohomology is the published right-derived
scheme-module functor.

`isZero_relativeCohomology_baseChange_of_isZero` concerns a smooth proper
`f : X ⟶ Spec R`, a line bundle `L`, and an arbitrary ring map `φ : R ⟶ S`.
If every relative cohomology module of `L` over `R` is zero, then every
relative cohomology module of its pullback to `X ×_Spec R Spec S` is zero.
It extracts the single strictly perfect representative supplied by the
published `universalPerfectSections` theorem. The published
`DerivedPlus.acyclic_of_iso_derivedComplex` combines natural-degree vanishing
with negative-degree vanishing of the right-derived functor to show that
this representative is acyclic in all integer degrees. Its projective terms
are flat. The published `ModuleComplex.exactAt_baseChange_of_flat` preserves
acyclicity under the arbitrary ring map using its strict upper bound.
The universal comparison and
`DerivedPlus.isZero_rightDerived_of_iso_derivedComplex` then give vanishing
of the actual relative cohomology on the pullback scheme. The ring map is
not assumed flat.

`affineSubordinateBasis x` is the set of affine opens `W` of `T` for which
there is an affine open `V` of `Y` with `W ≤ x ⁻¹ᵁ V`, for any morphism
`x : T ⟶ Y`. `isBasis_affineOpens_subordinate` proves that this set forms a
topological basis. The proof refines a neighborhood of
a point first by the inverse image of an affine neighborhood in `Y`, then
by an affine neighborhood in `T`. No quasi-compactness assumption is used.

`isZero_openCohomology_pullback_of_affineRestrict` applies to a smooth proper
`f : X ⟶ Y`, a line bundle `Q`, an arbitrary `x : Spec R ⟶ Y`, and affine
opens `V` of `Y` and `W` of `Spec R` with `W ≤ x ⁻¹ᵁ V`. Its hypothesis
is vanishing in every degree over `affineRestrict f hV`, with coefficient
the pullback of `Q` to `f ⁻¹ᵁ V`. Its conclusion is vanishing in the chosen
degree over the inverse image of `W` under the projection
`X ×_Y Spec R ⟶ Spec R`, with the restriction of the pulled-back coefficient.
The ring map is `x.appLE V W hWV`. Mathlib's
`IsAffineOpen.SpecMap_appLE_fromSpec` identifies its induced scheme map.
The proof applies the affine scalar-change lemma, pastes the two pullback
squares, and uses the published cohomology transport under isomorphic
pullbacks and independence of the chosen affine base. Pullback composition
and the restriction-pullback isomorphism identify the coefficients.

`isZero_relativeCohomology_pullback_of_affineRestricts` assembles this local
argument. It assumes the same vanishing over the inverse images of every
affine open of `Y`, and concludes vanishing after every affine base change.
For each degree, the subordinate basis and the preceding lemma satisfy the
published `isZero_higherDirectImage_of_isBasis` criterion for the projection
`X ×_Y Spec R ⟶ Spec R`. Every direct image of that projection is therefore
zero. The published `isZero_relativeCohomology_of_higherDirectImage`, applied
with the identity of `Spec R`, gives the conclusion. The hypothesis about
all affine restrictions is explicit here; this module alone does not
identify it with vanishing of all direct images of the original `f`.

These are derived consequences of published Library results and Mathlib
pullback geometry, rather than transcriptions of a source theorem. The
perfect-representative input follows the registered Stacks source
`stacks-perfect-complexes-a04446e5`, `perfect.tex`, tag 0A1I
(lines 7443–7455) and tag 0B91 (lines 7524–7544), at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. The present proof uses the proved
universal comparison, with its actual ordinary scalar-extension complex;
it does not assume the proposition stating that comparison.
