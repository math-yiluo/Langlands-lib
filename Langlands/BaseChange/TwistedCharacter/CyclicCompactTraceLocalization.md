# Localization of the compact trace tests in cyclic semisimple descent

For a characteristic-zero cyclic algebra, let \(T\) be the slice distribution
for the ordinary character of an irreducible admissible representation of
the cyclic matrix semidirect product at a semisimple adjoint element. The
pushforward and the Haar tensor identity are those of the normalized
conjugation map on the fixed algebra. Assume exponential product
straightening for the ambient matrix algebra. Use the regular trace
pairing and its restriction to the fixed algebra with a nontrivial
unitary additive character of the ground field.

Fix \(d\) of norm greater than one and an open neighborhood \(V\) of the
nilpotent points of the fixed-algebra annulus \(1/\|d\|\le\|x\|\le1\).
`cyclicCompactTraceLocalization` gives a positive radius bound and a
frequency bound. For any slice norm level below the radius bound and
inside the descent domain, take a smooth finite-dimensional compact type
with the specified exponential orbit trace formula. If \(T\) is nonzero
on the trace test extended in the unit-minus-one chart, some frequency in
the slice orbit modulo its dual lattice satisfies the following condition.
If its norm exceeds the frequency bound, it has a nonzero scalar rescaling
in \(V\) and in the annulus.

A small ambient norm subgroup fixes a nonzero vector of the ambient
representation. Its dual lattice has all cyclic adjoint images in the
unit-conjugation saturation of one compact set. Compact smoothing and the
descent pairing give an ambient orbit for any nonzero slice evaluation.
The three frequency matches give an orbit point in this saturation, a
point whose adjoint by the translated slice element is in the same orbit,
and a point whose fixed projection lies in the slice orbit. The uniform
inverse estimate on the directions transverse to the fixed algebra and
the small conjugation displacement give the hypotheses of
`projectedOrbitNearNilpotents`. That theorem supplies the rescaling of the
projected point. This is the compact trace localization step of Clozel's
Lemma 12. [Clozel 1987, §§3.6–3.7, printed pp. 158–165](https://doi.org/10.4153/CJM-1987-008-3)
