# Finite normal subgroups detected by unipotent matrices

This derived helper extends the published algebraically closed-field theorem
`isFinite_of_normal_of_unipotentPointMatrices` to a connected reductive group
over any field. It retains the full closed normal subgroup, including its
possible nonreduced structure. The ambient representation is required to be a
closed immersion, and the restricted matrices must have nilpotent deviation
from the identity on every relative scheme test.

The proof extends the subgroup and representation to an algebraic closure.
Closedness and normality survive this base change. The point-matrix comparison
and pullback adjunction transfer the all-test nilpotence hypothesis without any
assumption about semisimplicity after scalar extension. The geometric-radical
clause of reductivity supplies the algebraically closed theorem's hypothesis.
Finally, fpqc descent of finite morphisms reflects finiteness of the subgroup's
structure map to the original field.

Provenance: internal transport and descent of the cited Library theorem. This
is an ingredient of the composition-factor proof of Milne, *Algebraic Groups*
(2017), Proposition 21.60 (a) implies (d); it does not assert that the kernel is
smooth or trivial.
