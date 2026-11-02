# Reflection of ampleness of the same line bundle under field extension

`fieldBaseChangeAmpleReflection` proves the published proposition
`FieldBaseChangeAmpleReflectionStatement` in arbitrary universe `u`. For any
scheme `X` over a field `k`, any morphism `Spec K → Spec k` from a field
spectrum, and the specified actual line bundle `L` on `X`, ampleness of its
actual pullback implies ampleness of that same `L`. The theorem has no
additional outer assumptions.

The implemented proof uses ordinary sections and their supports. The
topological preparation derives compactness and quasi-separatedness of `X`
from the ample pullback. At a point `x`, choose an affine open `U` containing
it. The supported positive-power construction supplies a point `y` above `x`,
a positive integer `r`, and a section `t` of the actual pullback of `L^r`.
This section generates at `y` and vanishes on the full base change of the
closed complement of `U`. This last vanishing uses a sufficiently high
positive power; it does not replace that fiber product by its reduction.

Set `M = L^r`. The canonical scalar sections maps for `M` on `X` and for its
restriction to the closed complement are isomorphisms by the imported QCQS
sections comparisons. These comparisons derive their geometric hypotheses
from the ample pullback, and flatness from the field structure. The
coefficient extraction theorem applies to these exact canonical maps.
It supplies a section `s` of the same actual `M`, vanishing on the downstairs
closed complement and generating at the image of `y`, which is `x`.
Its proof uses exactness of scalar extension on the restriction kernel and
a nonzero residue observation to select a generating coefficient.

Vanishing on the complement puts the whole generation open of `s` inside
`U`. The affine generation-locus intersection theorem then proves that this
whole open is affine. The positive exponent, generation at `x`, this
affineness, and the previously proved compactness give exactly the published
definition of `L.IsAmple`.

This is an internal assembly of the imported support, nilpotence, actual
tensor-power comparison, canonical QCQS sections, coefficient extraction and
affine generation-open results. Its route differs from the relative-ampleness
and fpqc-descent route documented with the target. It uses neither the parent
cubic cohomology theorem nor an unproved descent or comparison premise.
Arbitrary characteristics, infinite and inseparable field extensions, and
arbitrary schemes remain allowed; no finiteness, reducedness, separatedness or
properness hypothesis is added.
