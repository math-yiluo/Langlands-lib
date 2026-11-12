# Uniform integral lifts for algebraic spaces

This derived internal construction combines the published algebraic-space
finite-field lifts and smooth Henselian lifts. It supplies part of the
integral-surjectivity argument needed for Conrad's Theorem 5.9.

`surjective_of_bound` retains an arbitrary original coefficient ring `C`.
Given a smooth space morphism, a Henselian local `C`-algebra `R` and a
surjective `C`-algebra map to a field `κ`, it assumes the numerical Lang–Weil
bound on every actual residue-point fibre. If the field cardinality exceeds
the square of the nonnegative error constant, the published numerical helper
gives surjectivity on residue points. The published smooth Henselian lifting
theorem then gives surjectivity on actual `R`-points. The numerical helper
also covers relative dimension zero.

`pointLifts` assumes the exact `SpaceUniformLangWeilStatement`, a
quasi-separated base of finite type over the lifted integers, and a separated,
quasi-compact, surjective morphism with geometrically connected fibres.
It takes an actual étale morphism chart with surjective source whose scheme
map is smooth of relative dimension `d`. This chart also proves that the
space morphism is smooth, so no additional smoothness assumption is needed.

The finite-field construction chooses one positive constant before any
local coefficient ring, finite field, coefficient algebra, quotient map or
target point is supplied. For every Henselian local ring with a surjective
finite-field quotient larger than this squared constant, it chooses a source
residue point above the reduction of the target point, lifts it by the
published Henselian theorem, and returns an actual integral source point
with the exact target equation.

The estimate and fixed-dimension chart remain explicit inputs. This module
does not prove the estimate, decompose varying dimensions, construct
arithmetic models or establish adelic openness. Its provenance is the
composition of the two published lifting results described above.
