# Reductivity ascent along an affine quotient with torus kernel

This internal supporting result for common domination of actual z-extensions
uses the Library definitions of an actual fppf quotient, a torus, and connected
reductivity. It does not require centrality of the kernel.

`HasTrivialUnipotentRadical.of_torusKernel` concerns affine groups over any
field, a target locally of finite type, and an actual fppf quotient whose
full scheme-theoretic kernel is represented by a closed torus inclusion.
If the target has trivial ground-field unipotent radical, so does the source.
For each candidate smooth connected normal unipotent subgroup of the source,
the proof forms its schematic image in the target. This image is smooth,
connected, unipotent and normal, by the published homomorphism-image,
unipotent-quotient and fpqc-normality results. Target radical triviality
kills it. The original subgroup therefore factors through the full torus
kernel; unipotent-to-torus homomorphism triviality kills that subgroup.

`IsConnectedReductive.of_torusKernel` assumes in addition that the target is
connected reductive, while retaining affine source as an explicit hypothesis.
Smoothness of the represented torus kernel makes the fppf projection smooth.
Geometric connectedness of the torus passes to the actual kernel and then to
the projection, giving connectedness of the source. After base change to an
algebraic closure, the preceding radical argument applies to the base-changed
torus and quotient. These are exactly the four fields of the Library's
connected-reductivity predicate.

The provenance is a derived geometric helper for Task 6660, rather than a
separately quoted proposition from the literature. It supplies the reductivity
step for the fiber-product construction underlying KP Fact 11.4.2 and
Lemma 11.4.3. The implemented argument uses only the existing Library results
listed in the imports.

`torusKernelReductiveAscent` packages the connected-reductivity result as the
exact proposition `TorusKernelReductiveAscentStatement`, with no extra premise.
