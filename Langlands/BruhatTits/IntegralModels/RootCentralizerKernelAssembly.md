# Full ambient kernels from root and centralizer kernels

This internal construction supplies compatible source and target charts for an
arbitrary homomorphism of smooth connected affine groups over an algebraically
closed field. A split torus acts through the source. The target root support must
be contained in the source support, and distinct indivisible source roots must
have disjoint positive integral rays. Every full source-root composite kernel
and one full whole-torus-centralizer composite kernel must be smooth.

The proof chooses a generic cocharacter and common finite lists of negative and
positive indivisible source roots. Dynamic root products indexed by those lists
exist on both groups, including rays with missing target roots. The full target
centralizer is represented by the generic dynamic centralizer. The `chartData`
construction concatenates the negative roots, full centralizer and
positive roots. Root maps and the centralizer map induced by the original
homomorphism give an exact compatible square for each factor. Both actual
ordered multiplication charts are open. Monicity of target factor inclusions
identifies each factor-map kernel with the corresponding original composite
kernel. The ordered open-kernel chart theorem gives smoothness of the full
ambient scheme-theoretic kernel.

The file also transfers full composite-kernel smoothness between arbitrary full
representatives of the same subgroup functor. All comparisons hold on every test
scheme. The result is derived from the existing dynamic, ordered-product,
centralizer and full-kernel interfaces; it assumes no smoothness of the original
homomorphism. Model-specific verification of its hypotheses remains separate.
