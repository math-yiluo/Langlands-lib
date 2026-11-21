# Compact finiteness of an adelic tensor

`compactPlaceAction` pulls the compact action at a place back along the
actual product coordinates of the standard infinite compact group. The
compact group acts trivially in the finite slot. The resulting diagonal
tensor is the compact action used by `tensorFreeAction`.

`tensorCompactAction_finite_continuous` proves local finiteness and
continuity of all scalar coefficients from the corresponding local
properties. The orbit of a pure tensor is in the image of the tensor of
the finite-dimensional orbit spans of its factors. To prove continuity,
expand in bases of these spans and extend the coordinate functionals to
the factor spaces. The coefficients of the pure tensor are finite sums
of products of continuous coefficients of its factors. The inverse of
the continuous compact coordinate parametrization is continuous by
compactness and Hausdorffness. Linearity extends both conclusions to all
tensors.

The finite translation action commutes with this compact action because
it operates on the finite slot alone. Smoothness for finite translation
follows by using an open stabilizer of the finite factor on a pure tensor
and intersecting the stabilizers when adding tensors.

The proof is an internal use of the algebraic tensor picture in Flath,
*Decomposition of representations into tensor products* (1979), §3,
printed pp. 181–182 (Corvallis Part I PDF pp. 177–178). The hypotheses
supply the compact representation used in the finite-dimensional
projection argument of Langlands, *On the notion of an automorphic
representation* (1979), Lemma 7, printed pp. 205–206 (PDF pp. 200–201).
