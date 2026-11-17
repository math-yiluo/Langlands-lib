# Comparison and kernel geometry of arbitrary fppf quotients

Worker 358.

All results apply over an arbitrary base scheme and use the actual fppf
quotient predicate `RelativeRoot.IsFppfQuotient F q`, including its equality
between the full kernel range and the subgroup functor `F`.

`FppfQuotientComparison.fppfHom` and `fppfIso` give the canonical comparison
map and isomorphism between two actual quotients of the same source by `F`.
The lemmas `fppfHom_fac` and `fppfIso_fac` assert compatibility with the
original quotient maps. No quasi-compactness assumption on either quotient
map is needed. Each comparison map is obtained from the published
`FppfHomDescent.hom`, since the other quotient kills the same full kernel.
The published quotient `hom_ext` proves that the comparisons are inverse.
`isAffineHom_target` transports affinity over the base from either target
to the other using this isomorphism.

If `z : Z ⟶ G` monomorphically represents `F`,
`RelativeRoot.IsFppfQuotient.kernelIso` identifies `Z` with
the actual kernel of `q` over the base. This follows from uniqueness
of representatives of a subgroup functor. The kernel square is a
pullback of `q` along the unit section, so it is flat and locally of
finite presentation over the base. Transport along the isomorphism gives
`flat_representedKernel` and
`locallyOfFinitePresentation_representedKernel`.

These are internal derived consequences of the imported Library APIs:
fppf homomorphism descent, actual kernel pullbacks, and uniqueness of
represented subgroups. They provide geometry needed when a quotient
target is supplied without affinity or quasi-compactness hypotheses.

The canonical quotient comparisons are reused from `FppfQuotientUniqueness`.
The represented-kernel isomorphism is the existing
`RelativeRoot.IsFppfQuotient.kernelIso` from `Rational.FppfQuotientSmooth`.
