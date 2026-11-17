# Isolation of points in analytic étale fibres

This internal derived helper proves that every point of a quasifinite strong
analytic map has an open neighborhood containing no other point in its fibre.
It uses the published definitions and finite-fibre theorem and makes no claim
to be a verbatim statement of external literature.

Local Hausdorff neighborhoods imply that the source is T1: a specialization
lies in any neighborhood of its target, so both points lie in one Hausdorff
subspace and are equal. At the chosen point, quasifiniteness supplies open sets
on which the map is finite. A recognized target affinoid containing the image
then gives a finite fibre in the source neighborhood. Removing all other points
of this finite set gives the required open neighborhood.

For a localized étale arrow, use its defining arrow isomorphism to a strong
étale representative. The inverse source isomorphism pulls back the isolating
open set. Its underlying map is a homeomorphism, so its injectivity and the
arrow's commuting square transport fibre isolation back to the original source.
