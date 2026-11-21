# Geometric points of the analytic étale site

`Langlands.Analytic.SaturatedAtlasPresentation.EtaleSite.geometricPointStatement`
proves the Library's `GeometricPointStatement.{u, v, uL}`. For a complete
ultrametric ground field `K : Type u`, a complete algebraically closed
ultrametric extension `L : Type uL` with `NormedAlgebra K L`, an analytic space
`X : LocalizedCategory.{u, v, v} (K := K)`, and an `L`-valued point `x` of `X`,
the category of elements of `pointFibre L x` is cofiltered and every covering
sieve of `etaleTopology X` is jointly surjective on the fibres. The three
universes are independent. [Target statement](EtaleGeometricPointStatement.md)

The proof gives `geometricPointStatement_of_etalePullbacks_and_imageLift` its
finite-diagram and image-lifting inputs. `localizedEtaleStability` supplies
composition and right cancellation, `localizedEtalePullbackBaseChange` supplies
pullbacks with an étale base-changed projection, and
`localizedEtaleFieldPointPullback` makes those squares pullbacks on full
`L`-valued points. The reduction refines two fibre elements by the pullback of
their étale objects over `X`. It equalizes parallel arrows by pulling back the
étale diagonal along the pair of arrows. In each case the pullback on field
points supplies the lift with the prescribed evaluations. The identity of
`X` supplies the nonempty fibre element.
[Finite-diagram reduction](EtaleGeometricPointPullbacks.md),
[étale stability](EtalePointwiseLifting/LocalizedStability.md),
[base change](LocalizedEtalePullbackProof.md),
[field-point pullbacks](LocalizedEtaleFieldPointPullbackProof.md)

For image lifting, `strongEtaleFieldPointImageLift` extends the prescribed
evaluation along the finite completed residue field extension and constructs
a compatible point on all charts. `geometricPointImageLift_of_strong` uses
right cancellation to make the underlying arrow between étale objects étale,
then transports the lift through the arrow isomorphism to a strong
representative. A jointly surjective presieve thus lifts each fibre element.
The categorical reduction uses cofilteredness to obtain pointwise lifting
squares and extends joint surjectivity to all sieves of the generated
Grothendieck topology.
[Strong field-point lifts](FullRecognitionFieldPointLifts.md),
[transport](EtaleGeometricPointImageTransport.md),
[point axioms and generated topology](EtaleGeometricPointGeometry.md)

The Lean proof assembles these Library theorems. The stalk construction in
Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
§4.2, printed p. 87, provides the geometric context. [Original edition](https://www.numdam.org/item/PMIHES_1993__78__5_0/)
