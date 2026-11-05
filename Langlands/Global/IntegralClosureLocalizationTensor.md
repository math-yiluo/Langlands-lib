# Original integral closure after lower localization

This derived construction supplies the coefficient-localization step for the
actual integral factors in Conrad, *Weil and Grothendieck approaches to adelic
points* (2011), Example 4.2, printed pages 9–10. It is used to pass from the
actual global S-integer integral closure to the integral closure of an original
lower local ring.

For commutative rings R, V, B and L, suppose V is a localization of R at a
specified multiplicative set and B is an actual integral closure of R in L.
The compatible original scalar towers into L are explicit.
`integralClosureLocalizationTensorEquiv` constructs a V-algebra equivalence
from V tensored with B over R to the actual integral-closure subalgebra of V in
L. No isomorphism with the desired localized closure is supplied as input.

The construction first uses the canonical integral-closure algebra equivalence
to replace B by the standard integral-closure subalgebra of R in L. Tensoring
this equivalence retains the V-factor. Mathlib's proved localization comparison
`TensorProduct.toIntegralClosure_bijective_of_isLocalization` then identifies
that tensor with the integral closure of V in V tensored with L over R.
Since L is already a V-algebra, the localization algebra unit identifies that
last coefficient tensor with the original L. Mapping the integral closure
through this actual algebra equivalence completes the construction.

The pure-tensor formula sends a tensor of a V-element a and a B-element b,
viewed in the original L, to the product of their original coefficient images.
It follows from the tensor comparison and localization unit formulas and the
canonical integral-closure equivalence's original inclusion identity. In
particular the right tensor factor retains the original B-to-L map.

The four rings have independent arbitrary universes. The result needs no
field, Noetherian, Dedekind, finite-extension or separability assumptions.
The localization and integral-closure premises concern given original rings;
the corresponding arithmetic instances have been proved separately. Their
original-place instantiation, completed-integer tensor decomposition and adelic
point comparison remain obligations of the host task.
