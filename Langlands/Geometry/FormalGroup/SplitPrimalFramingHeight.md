# Height-zero split primal rigidifiers and their Drinfeld triples

`Harris.HasPrimalChartHeightZero` measures the projected polarized rigidifier
on the reduced target's actual principal cover. On the source it uses the
division retraction of the extended fixed frame. On the target it uses the
reduced division image retraction of the actual polarized module. On every
test algebra the projected section must have signed kernel-rank height zero
with the prime as scalar and with ranks measured in powers of the prime.

`Harris.primalFramingSourceAtlas_hasHeightSquared` transfers the actual
square-height certificate of the frame along the residue coefficient map and
onto the source's principal cover. In `Harris.primalAtlasFraming_height_zero`,
the inverse integral source comparison transfers these ranks to the chart
laws that measure the centralized tensor. The central height comparison uses
the scalar identity `p = u ϖ^e`, where `u` is an integral unit. The integral
source and target comparisons then preserve zero height in the final
coordinates of the Drinfeld rigidifier.

`Harris.primalDrinfeldFramedAtlasOfLocalHeight` constructs the actual framed
triple. For a positive ramification exponent and residue cardinality `p^f`,
it obtains square height on the special target from the verified ramified
height theorem, and obtains zero chart height for the framing from the local
projected condition. It takes a square-height special frame and the field
certificate on the residue coefficient ring as inputs.

The construction formalizes the primal component of the split comparison in
Rapoport–Zink, (6.17) and Lemma 6.44, printed pp. 309–310. The input condition
can be applied once the chosen Harris component of the polarized moduli has
been expressed in terms of these prime-normalized heights.
