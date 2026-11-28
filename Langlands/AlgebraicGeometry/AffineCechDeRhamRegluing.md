# Regluing a marked scheme along square-zero transitions

Let \(X\) be smooth and separated over \(\operatorname{Spec}R\) with a
finite affine cover and a finite free differential frame. For a
square-zero base ideal \(I\) and representatives in
`HodgeSummandCocycles`, the transition on each pair intersection is the
scheme map defined by the algebra map `transition` in the direction from
the second chart to the first. Its reduction is the identity of the
actual reduced overlap, so it fixes points. The identity and composition
of the affine endomorphisms and their compatibility with restriction
yield the twisted open-gluing datum `regluingData`.

The maps are over \(\operatorname{Spec}R\), so the pieces give the
structure morphism `regluedMap`. It is smooth on the cover by the
pieces. The base-changed transitions agree with the original inclusions
on reduction, giving `regluedMarking` from the actual reduction of \(X\)
to the actual reduction of the new scheme over \(\operatorname{Spec}(R/I)\).
If the original reduction is proper over the quotient base, properness
of the reglued map follows from reflection along the surjective closed
quotient. The cover `regluedCover` has the original chart indices.
`regluedMarking_matches_charts` matches the reduced opens, and
`regluedChart_reduces` computes the reduction of each thicker chart map.
On any affine open inside two original charts,
`regluedChart_transition` computes how their maps into the reglued scheme
differ.

The construction applies the affine square-zero gluing procedure of
Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, §2.1.3. Here the overlap derivations come from the
function components of cocycles representing a lifted summand for the
application to Proposition 2.1.6.8. The retained source is
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
