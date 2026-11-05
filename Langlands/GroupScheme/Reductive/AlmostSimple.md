# Almost-simple field group schemes

Author: Worker 1454.

`IsAlmostSimple G` is a proposition for an actual group scheme over an arbitrary
field `k : Type u`, at every universe `u`. It requires the published
`IsSemisimple G`, noncommutativity on the functor of points, and the assertion
that every smooth connected closed normal subgroup has range either the
identity subgroup functor or the whole subgroup functor. Closedness and
normality retain their published all-test meanings. The definition asserts no
existence or decomposition theorem.

The source is J. S. Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, Definition 19.7, printed p.399, together with the
author's correction to that definition in
`milne-2017-algebraic-groups-errata-2026-11-02`. The corrected definition
explicitly requires semisimplicity and noncommutativity and tests smooth
connected normal subgroups. It does not require every proper subgroup scheme,
including a nonsmooth one, to be finite. The all-test range formulations express
that the actual inclusion is the trivial or total subgroup, respectively.

The related Theorem 21.51, printed pp.440–441, concerns normal almost-simple
factors. The official errata also state that its proof was rewritten in the
2022 reprint; this definition supplies no proof of that theorem and does not
rely on the uncorrected argument.
