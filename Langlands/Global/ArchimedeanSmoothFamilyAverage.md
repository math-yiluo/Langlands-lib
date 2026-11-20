# Compact averages of simultaneous right translations

`SmoothFamily.averageLM` applies the Library's smooth compact-index average in every coordinate with the same parameter map, measure, and weight.

The proof embeds the family into the product of the spaces of continuous functions on compact sets, with one such coordinate for every original index, enveloping derivative, and compact set. The existing derivative topology on each smooth function gives the product embedding. A continuous complex linear functional on the family extends along this embedding as a real linear functional and then factors through a finite set of normed coordinates. In that finite product, the Bochner integral commutes with the continuous linear functional. Point evaluations identify the integral of the weighted orbit in each coordinate with the corresponding derivative of the smooth average by `envelopingDerivative_average`.

It follows that the average lies in the closure of any complex submodule containing the simultaneous translates in its closure. Each continuous complex linear functional annihilating the submodule also annihilates its closure and thus has zero integral on the weighted orbit. The complex Hahn–Banach separation lemma gives the result.

This internal construction extends the compact-index averaging used in `ArchimedeanCompactIndexApproximation.lean` to families. Its intended convolution application comes from Borel–Jacquet, *Automorphic forms and automorphic representations* (1979), §1.6 (2), printed p. 191, PDF p. 186.
