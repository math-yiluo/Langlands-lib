# The prescribed isobaric tensor and the ordered induction tensor

The source action uses the finite induction tensor of the given restricted
tensor diagram and the real and complex standard modules of the cuspidal
parameters in the original block order. The target action uses the finite
constituent tensor of the same diagram and the chosen quotients of the
ordered real and complex standard modules. Both actions use the common
free operator algebra.

`targetTensorAction_subquotient` takes the finite adelic subquotient from the
diagram and the compact and Lie subquotient maps of the archimedean
constituents. It tensors their inclusions and quotient maps. The tensor of
the inclusions is injective and the tensor of the quotient maps is
surjective. The image of the tensor inclusion is an invariant subspace of
the source, and its range equivalence carries the surjection to that
subspace. The target has the specified operators at every place.

These models implement the local constituents and their tensor in Langlands
(1979), Lemma 1, printed p. 203 (Corvallis I PDF p. 198). They use the local
induced constituents appearing in Getz–Hahn (2024), Theorems 10.6.4 and
10.7.5, printed pp. 286 and 288 (PDF pp. 298 and 300).
