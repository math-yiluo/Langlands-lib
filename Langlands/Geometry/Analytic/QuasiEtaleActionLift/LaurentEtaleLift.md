# Nearby finite étale lifts over a Laurent neighborhood

`BoundedAlgHom.HasSpectralLiftsOver` packages the local bounded-algebra
lifting property used in the proof of Berkovich's *Vanishing cycles for
formal schemes* (1994), §7, Key Lemma 7.2. It is an internal formulation
for maps out of a presented affinoid algebra. A finite set of output
elements and a positive tolerance determine a finite set of coefficient
elements and a positive tolerance. A reference map with spectrum image
in the prescribed locus and a perturbation passing the coefficient
tests extend to a nearby bounded lift. The tolerances are upper bounds
on displacement at every point of the test spectrum.

If the source algebra becomes standard étale after inverting an element,
take the rational chart where the element has a positive lower bound.
The spectrum units criterion makes its image invertible in the chart
algebra. The chart map thus factors through the algebraic localization,
and rational representability factors each admissible reference map
through the chart algebra. This is the setup of the standard étale
lifting lemma.

For a finite Banach affinoid map that is étale at a point, the algebraic
étale locus criterion applies to the kernel prime of the point.
The standard étale localization theorem supplies an element outside
that prime. Its value at the point is positive, so the Laurent chart
defined by half that value contains a neighborhood of the point. The
preceding construction gives the lifting property over its locus.
