# Lifting a reduced morphism that preserves the first Hodge step

`exists_lift_of_reductionPullbackH1_maps_hodgeF1` concerns a morphism
from the actual square-zero base reduction of a smooth separated scheme
to another smooth separated scheme over `Spec R`. The two finite affine
covers and their index map are compatible with the reduced morphism.
The reduced source has constant global functions. The target is supplied
with compatible closed forms that restrict to bases of its relative
cotangent modules on the tuple intersections. If the corrected pullback
on degree-one Čech–de Rham cohomology carries the target's first Hodge
step into that of the source, the reduced morphism lifts to an actual
morphism of the thicker schemes over `Spec R`.

Choose affine lifts and use lift independence to compute the corrected
pullback with those lifts. On each target basis form, Hodge preservation
gives a function primitive for the overlap contractions. The primitive
normalization makes these cochains ideal-valued, so they define local
algebra corrections with the prescribed reduction. The correction
identities show that the two maps on each affine overlap agree.

`exists_lift_of_compatible_sections` passes to the spectra of the actual
section rings. The maps into the overlap affine opens agree with the
vertex maps under the open immersions. They give the compatibility for
gluing along the affine open cover. Check the base equation on the
thicker charts using the algebra structure maps. Check the reduction
equation on the preimages of these charts, where the ring maps agree
with those of the given morphism.

This is an affine Čech implementation of the converse morphism criterion
in Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, Proposition 2.1.6.9, printed p. 136 (PDF p. 164).
The construction computes the pullback for fixed compatible covers and
exposes the geometric hypotheses on the basis and the global functions.
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
