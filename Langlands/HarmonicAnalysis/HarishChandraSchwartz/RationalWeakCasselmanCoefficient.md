# Weak constant term of a normalized Casselman coefficient

`Langlands.BruhatTits.SpecialCompact.StandardWeakTensorCasselmanStatement`
identifies the Library's weak projection of the chosen standard constant term
of a coefficient tensor of an admissible smooth representation. Given a
stable Casselman pairing for the standard parabolic and the compatible
compact-open normal basis, the formula pairs the unitary projections of the
two Jacquet classes. On a pure tensor \(v \otimes \ell\), its value at \(m\) is
\(b(p^\vee[\ell], r(m)p[v])\). Here \(b\) takes the opposite Jacquet class
first, \(r\) is the action on the ordinary coinvariants twisted by the inverse
half of `standardRadicalModulus`, and the opposite action uses the reciprocal
twist. Both projections use the rational points of the same standard split
component. The tensor map extends the pure-tensor formula by linearity.

This is the coefficient projection step in the proof of Waldspurger
III.5.1 (printed p. 270), in the form used in the first coefficient equality
in V.1.1 (printed p. 290). The Lean proposition is derived for actual standard
parabolic data in the Library. The subsequent identification of the pairing
with a sum of lower-Levi pairings uses separate results.

`isCompl_unitaryWeightPart` applies the central generalized-weight
decomposition of an admissible representation. A coefficient of a vector
in a unitary weight space belongs to `weakExponentSpace`, and a coefficient
of a nonunitary weight vector belongs to `positiveExponentSpace`. The
uniqueness lemma `weakPart_eq_of_mem` gives the projection on the source
vector. Invariance of the bilinear pairing moves right translation by a
central component element to the inverse action on the other vector. The
nonunitary part of that vector contributes an element of
`positiveExponentSpace` since inversion preserves nonunitarity. With the
source vector already projected, the same coefficient lies in
`weakExponentSpace`, and disjointness makes it zero.

The two orientations of the Iwahori contraction basis give admissibility
of both normalized actions. `IsStablePairing.map_action` gives invariance
before twisting, and the reciprocal scalar factors cancel. The proof
identifies the two linear maps on tensors by evaluating them on pure
tensors, using `weakPartLinear` on the sum of the exponent spaces and the
right-finiteness supplied by `coefficientTensorConstantTerm_spec`.
`standardConstantTerm_coefficientTensorMap` then identifies the tensor
constant term with the Library's chosen standard constant term.

Source reference is J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, 2003, III.5.1 and V.1.1,
registered as `waldspurger-2003-plancherel`.
