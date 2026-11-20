# Adjoint Hasse reduction to the models of the central kernel

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994),
§6.5, pp. 331–332, give the centers of simply connected absolutely
simple groups by inner type. The center is the kernel of the simply
connected cover onto the adjoint group, as used in their Theorem 6.22,
pp. 336–337. In Lean, a flat surjective homomorphism sends the full
center into the full center. Since the target is adjoint, the source
center maps to the identity. Together with centrality of the isogeny
this identifies the actual kernel as a representative of the full
scheme-theoretic center. Almost-simplicity ascends to the semisimple
cover over the original field and after extension to its algebraic
closure.

The center classification proposition asks for an actual isomorphism
from the kernel of any simply connected cover of an absolutely
almost-simple adjoint group over a number field to one of four models.
They are a roots-of-unity group of positive exponent, a finite split
product of such groups, the positive-exponent torsion in the Weil
multiplicative group of a number field extension, or its norm-one
torsion of quadratic degree or degree coprime to the exponent.
These families include the entries of the source table with wider
exponent and degree ranges where the arithmetic lemmas apply. The
trivial entry is represented by exponent one. In the norm-one
trialitarian cases the extension has degree three and the exponent
is two. The proposition keeps only the model information needed
for the arithmetic reductions.

Given the classification and the simply connected Hasse kernel,
choose the published simply connected cover and apply the arithmetic
kernel theorem for its model. The adjoint Weil and product reductions
then give the general adjoint Hasse kernel. The combined reduction
uses the absolute simply connected kernel, these actual center
models, and quadratic isometry to reach the exact published Hasse
principle for finite separable covers.

This is a derived classification input and a conditional assembly
for Milne, *Algebraic Groups* (2017), Theorem 25.64, p. 562.
