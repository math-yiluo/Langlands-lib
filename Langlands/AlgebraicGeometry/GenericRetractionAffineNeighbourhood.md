# Affine neighbourhoods from generic retractions

This derived construction combines the dominant-section and rational-map
stalk-extension interfaces for the finite-type stage in the proof of
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §6.4 Lemma 4.
It does not yet construct the semilocal intersection from the normal
codimension-one hypotheses.

Suppose `X` is integral and separated and `Z` is reduced and affine, in any
universe. Let `f : Z ⟶ X`. The theorem
`rationalMap_generic_retraction_section` considers a rational map
`r : X.RationalMap Z` whose generic restriction is dominant and whose
composite with `f` is the canonical map from `Spec X.functionField` into
`X`. It proves that the maximal partial map of `r` is dominant and that
its composite with `f` is the open inclusion of its domain.

Dominance follows because the dominant generic restriction factors
through the partial map. The section equation follows by identifying
its composite as a rational map with the identity at the generic
point, then applying separatedness to obtain equality on the whole
domain.

The constructor `affineNeighbourhoodOfGenericRetraction` works over any
scheme `S`. It takes `p : X ⟶ S`, a locally finite type morphism
`q : Z ⟶ S`, and `f` over `S`. It also takes a dominant generic inverse
`a : Spec X.functionField ⟶ Z`, a finite set `E`, and for each `x ∈ E`
a morphism `Spec (X.presheaf.stalk x) ⟶ Z` over `S` agreeing with `a`
at the generic point. It returns an actual affine open of `X`
containing `E`.

The constructor spreads out `a` to a rational map. The stalk extensions
put every point of `E` into its domain. The preceding theorem produces a
dominant section there, and `affineNeighbourhoodOfDominantSection`
constructs the affine open by finite prime avoidance. The generic
inverse, finite-type affine stage, and stalk extensions remain explicit
inputs to this supporting construction.
