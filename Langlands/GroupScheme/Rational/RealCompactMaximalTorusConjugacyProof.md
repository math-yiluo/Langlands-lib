# Maximal-torus conjugacy for compact real semisimple groups

`Langlands.GroupScheme.realCompactMaximalTorusConjugacy` proves
`RealCompactMaximalTorusConjugacyStatement`. For a semisimple group scheme
over the real numbers with compact full real-point group, it produces
a real point conjugating any two given maximal torus embeddings. The
conclusion is an equality of subgroup functors on every real test
scheme.

The proof takes a closed representation of the connected reductive
group with transpose-stable real matrix image. The affine point
homeomorphism and continuity of matrix evaluation transfer compactness
to this image. For each real matrix \(q\) in the image, \(q^*q\) is
positive definite and belongs to the same compact group. A positive
semidefinite element of a compact matrix subgroup is the identity,
so \(q^*=q^{-1}\). The difference between each transposed entry and its
corresponding inverse entry is a regular function on the group.
Smoothness gives reducedness and Zariski density of the real points
forces each of these functions to vanish. Consequently every complex
matrix \(q\) in the image satisfies \(q^*=\overline{q^{-1}}\).
The ambient image and both torus images are therefore stable under
adjoint, since they are stable under inverse and coefficient
conjugation.

Maximality persists under base change to the complex numbers, where
the published maximal-torus conjugacy theorem produces a conjugator.
The comparison between points of the base-changed group and complex
coefficient points transports it to a matrix \(g\) conjugating the
two torus images. Adjoint stability implies that \((g^*)^{-1}\) also
conjugates them in the same direction. Thus \(g^*g\) normalizes the
first image and belongs to the ambient image. The ambient image and
the normalizer of the first image are polynomially defined subgroups.
Closure under positive powers puts the positive square root \(a\) of
\(g^*g\) in both. The matrix \(u=ga^{-1}\) is unitary and conjugates
the same two images. The ambient identity \(u^*=\overline{u^{-1}}\)
then gives \(\overline{u}=u\).

Membership in the ambient image lifts \(u\) to a complex point of the
group. Faithfulness makes that point Galois-fixed, and finite Galois
descent produces a real point with that complex base change. The
conjugated complex torus images agree on complex points.
Both tori are smooth, so they are reduced and have dense complex points.
Closed subgroup containment from dense points upgrades both
inclusions to the full subgroup functors over the complex numbers.
Faithfully flat base change along \(\operatorname{Spec}\mathbb C
\to \operatorname{Spec}\mathbb R\) reflects that equality for
conjugation by the descended real point.

The statement corresponds to Theorem 2 on printed pages 19–20 of
Kazuo Suzuki, *A note on a theorem of E. Cartan*, Tohoku Mathematical
Journal 23 (1971), 17–20. The Lean proof uses the matrix polar
adjustment above. [Suzuki's article](https://doi.org/10.2748/tmj/1178242683)
