# Formal-scheme presentations on affine Nilp tests

`Nilp.FormalSchemePresentation F` exhibits a type-valued functor on affine nilpotent tests by an open cover of affine formal spectra. Each chart is the functor of an actual complete adic algebra whose ideal of definition contains the base parameter. Its points are the colimit of the points of the ordinary quotient schemes. The universe lift of the chart points allows the target functor to take values in a larger universe. `Nilp.IsFormalScheme F` asserts that such a presentation exists for the given functor.

`Nilp.IsZariskiLocal` is the gluing condition on the principal-open basis of each affine test. For a family of elements generating the unit ideal, one gives a point on each principal localization. The two actual localization maps to the localization at a product give the matching condition. A matching tuple has a unique global point.

`Nilp.OpenOnAffineTests` describes an inclusion of functors. For a point of the target over an affine test, its inverse image is specified by an open subset of the test spectrum. A map from another affine test lifts to the source exactly when the entire image of its spectrum is in that open. Objectwise injectivity makes the lift unique. The cover condition asks that these inverse images cover the underlying spectrum of every affine test at every target point.

This is the affine-test formulation of the Zariski-local functor with open affine formal spectrum charts in Rapoport and Zink, *Period Spaces for p-divisible Groups* (1996), §2.1, printed p. 49 (PDF p. 64). The powers of a single ideal give the adic charts considered here. Construction of the charts for a particular moduli functor is a separate representability assertion.
