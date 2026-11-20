# Reduced fibre theorem for schemes over a Nagata Dedekind domain

`SchemeReducedFibreStatement` formulates the Stacks Project, Theorem 37.65.1.
Let \(A\) be a Dedekind domain with fraction field \(K\). The Nagata hypothesis
asserts that \(A\) is Noetherian and, for every prime \(\mathfrak p\) of \(A\),
that the integral closure of \(A/\mathfrak p\) in any finite extension of its
fraction field is a finite \(A/\mathfrak p\)-module. Let \(X\) be flat and of
finite type over \(\operatorname{Spec}(A)\). The finite-type condition is
expressed by local finite type and quasi-compactness. [Theorem 37.65.1, Tag
09IL](https://stacks.math.columbia.edu/tag/09IL), [Nagata rings, Tag
032R](https://stacks.math.columbia.edu/tag/032R).

The proposition asks for a finite extension \(L/K\). Write \(B\) for the
integral closure of \(A\) in \(L\), \(W\) for the base change of \(X\) to
\(\operatorname{Spec}(B)\), and \(h\) for the map from the normalization of
\(W\) to \(\operatorname{Spec}(B)\). The conclusion provides a witness that
each quasi-compact open of \(W\) has finitely many irreducible components.
Every generic point of every scheme fibre of \(h\) lies in an open
neighbourhood in the normalization on which \(h\) is smooth. The witnesses
for \(W\) and the smooth neighbourhood are explicit in Lean. The universe of
\(K\) is independent of the universe of \(A\), \(L\), and the schemes.
[Theorem 37.65.1, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL),
[The normalized base change, Tag 09IK](https://stacks.math.columbia.edu/tag/09IK).

`genericPointResidueMorphism` is the canonical map from the coproduct of
spectra of the residue fields at the generic points of the irreducible
components. Each generic point in a quasi-compact open gives a generic point
of an irreducible component of that open. Finiteness of those components
makes the preimage a finite coproduct of compact spectra. The coproduct has a
disjoint affine open cover, so its source is quasi-separated and the map is
quasi-separated. `schemeNormalization` and `schemeNormalizationHom` use
Mathlib's relative normalization of this map. This gives the normalization
used in the source even when the original scheme has nilpotents. [Equation
29.55.0.1, Tag 035M](https://stacks.math.columbia.edu/tag/035M),
[Definition 29.55.1, Tag 035N](https://stacks.math.columbia.edu/tag/035N).

The statement is an input to the affine reduced-fibre reduction. Its
normalization and the open-neighbourhood formulation of smoothness match the
declaration for Tag 09IL in the retained AxiomMath Stacks source, commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`. [AxiomMath Stacks,
ReducedFibreTheorem.lean](https://github.com/AxiomMath/Stacks/blob/c496df0d9beea9deaeabcea8492605f9a0a2313b/StacksFrontier/AlgebraicGeometry/MoreMorphisms/ReducedFibreTheorem.lean#L378-L398).
