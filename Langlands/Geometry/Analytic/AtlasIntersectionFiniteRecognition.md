# Recognition of intersections from finite local algebra comparisons

Worker 1685 constructs a full local domain from a global candidate affinoid
algebra and finite local comparisons. This is internal infrastructure derived
from finite full-domain recognition and the actual local-domain category. It
does not assume a global intersection representation or spectral injectivity,
and it does not construct the candidate quotient algebra by ideal descent.

`Represents.postcomp_equiv` transports a full represented domain through an
actual bounded equivalence of its representing algebra. The base and literal
locus remain unchanged. Its proof uses the induced spectrum homeomorphism
for the range equation, and composes the full universal factors with the
bounded inverse equivalence for existence and uniqueness.

For local domains `U` and `V`, `FiniteIntersectionData` records a presented
affinoid `Q`, bounded maps `f : U.algebra → Q` and `g : V.algebra → Q`,
an actual finite full-domain cover of `Q`, local domains `Tᵢ` with actual
inclusions into both inputs, and bounded equivalences from each cover algebra
to `Tᵢ.algebra`. The two equations over `f` and `g` are equations of entire
bounded algebra maps. The union of the literal `Tᵢ` loci is the intersection.
Each cover component is saturated for `f`: its locus is exactly the inverse
image of the ambient locus of `Tᵢ` under the actual spectrum map of `f`
followed by `U.ambientMap`.

Transport of each local inclusion's full representation proves that the
composite from `U.algebra` to each cover algebra is a full domain. To prove
global spectral injectivity, choose a cover component containing the first
point. Saturation puts the second point with the same `f` image in that
component as well. Lift both points to the component spectrum; the spectrum
embedding of its full representation over `U.algebra` identifies the lifts.
Finite full-domain recognition then proves the global full universal property,
retaining exactly `Q` and `f`.

`intersection` extends this recognized domain through the original full
presentation of `U`. Saturation and the covering prove containment of its
ambient image in the union of the `Tᵢ`; the local spectrum comparisons and
surjectivity onto each `Tᵢ` prove the converse. Its ambient locus is therefore
the literal intersection of `U.locus` and `V.locus`.

The two inclusions are the canonical arrows constructed from this equality.
Thinness identifies the first restriction with `f`. For each local piece,
full representation over `U.algebra` identifies its entire restriction from
`Q` with the equivalence composed with the cover base map. Thinness then
compares the two routes to `V`, and finite full-domain cover detection of
equality proves that the second canonical restriction is exactly `g`.
This argument never treats equality of spectrum maps as faithfulness on
algebra maps, so it preserves nilpotent information.

Finally `tensor_isAdmissibleEpi` transfers admissibility of the genuine tensor
lift of `f` and `g` to the genuine tensor lift of the canonical inclusion
restrictions, using these exact bounded-map equalities. Admissibility of the
candidate map is an explicit hypothesis; construction of the global quotient,
its local comparisons and admissibility remains a separate obligation in the
full special-set intersection proof.

The coefficient, ambient-space and original-index universes are independent.
The coefficient field is complete and ultrametric. Arbitrary positive radii,
trivial valuations, nonreduced or zero quotients and empty domains remain in
scope; there is no global ambient Hausdorffness hypothesis.
