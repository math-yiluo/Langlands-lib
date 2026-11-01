# A finite affinoid test for two bounded maps

`FiniteJointImage f g` records an actual finite positive-polyradius presented
affinoid algebra `D`, bounded maps from the source presentations to `D`, and an
injective bounded algebra map from `D` to the common target. Composing with that
last map recovers `f` and `g`. Injectivity is algebraic; no inverse norm estimate
or closedness of the image in the target is asserted.

This is an internal construction derived from the published weighted evaluation
and quotient APIs. Its purpose is to supply a finite affinoid test in the proof
of spectrum injectivity for full domain representations. It does not establish
the analytic assertion that compatible points admit a common valued-field
realization.

`finiteJointImage` works for two arbitrary finite presented affinoids over an
ultrametric normed field, with bounded maps to a complete ultrametric normed
commutative algebra. The target may lie in a different universe. The coefficient
field need not be complete for this construction.

The implementation concatenates the two finite coordinate tuples and their
positive polyradii. The coordinate monomial bounds of `f` and `g` give the
bound for the concatenated tuple, so evaluation defines a bounded map from the
enlarged weighted Tate algebra. Its kernel is closed by continuity. The quotient
by this kernel is the actual presentation `D`, and quotient descent gives its
injective map to the target. The two variable inclusions descend through the
original source ideals: evaluation on each block is the corresponding source
map, as checked on coordinates by the weighted Tate universal property.
Surjectivity of the presentation maps then proves the two factorization
identities.

`FiniteJointImage.comp_eq` uses the injective map into the target to lift any
equation `f.comp i = g.comp j` to the corresponding equation between the two
maps into `D`. Empty coordinate blocks, zero quotient algebras, arbitrary
positive radii, and trivial valuations are retained throughout.
