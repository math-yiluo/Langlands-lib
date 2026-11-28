# Composition and marking isomorphisms on the square-zero reduction

Let \(I^2=0\) in a ring \(R\) and let \(X,Y,Z\) be smooth separated
schemes over \(\operatorname{Spec}R\) with finite affine covers. The map
`reducedSchemePullbackH1` takes an actual morphism
\(m\colon X_{R/I}\to Y_{R/I}\) over \(\operatorname{Spec}(R/I)\) and
an index map \(\beta\) sending each source chart to a target chart
compatible with \(m\) on reduction. It applies `reductionPullbackH1` to
the composite of \(m\) with the projection \(Y_{R/I}\to Y\).

For a second reduced morphism \(n\colon Y_{R/I}\to Z_{R/I}\) with
compatible index map \(\delta\), the two systems of locally lifted maps on
sections compose at every tuple and vertex. Reducing this composite on the
source chart gives the section map of the composite reduced morphism.
Indeed, the section maps of both local systems reduce to the actual
morphisms' section maps, which compose. The difference between the
composite and a chosen lift of the composite lies in the extended ideal on
every tuple intersection. The congruence comparison identifies the
degree-one maps, and `LocalPullbacks.pullbackH1_comp` gives
`reducedSchemePullbackH1_comp` with index map \(\delta\circ\beta\).

For the identity reduced morphism and the original chart at each vertex,
the system of identity section maps gives the same degree-one map by the
congruence comparison. Its contractions vanish, which proves
`reducedSchemePullbackH1_id` on cocycle representatives.
`reducedSchemePullbackH1_bijective` treats a reduced isomorphism with a
bijection of indices and with equality of the matched opens on the
reduction. The inverse isomorphism and the inverse index bijection supply
the inverse degree-one pullback by the composition and identity laws.

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, Proposition 2.1.6.4, printed pp. 133–135 (PDF
pp. 161–163), constructs the corrected pullback of a morphism on the
reduction. The composition and identity laws above follow from this
affine homotopy construction and functoriality on sections. They give
the marking result on fixed covers with matching reduced charts. The
retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
