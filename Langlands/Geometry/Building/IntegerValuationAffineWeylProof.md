# Integer-valuation affine root systems and affine Weyl containment

`Langlands.Geometry.Building.integerValuationAffineWeyl.{u}` proves exactly the
existing `IntegerValuationAffineWeylStatement.{u}`, at arbitrary universe `u`.
It retains every quantified input and the sole order-one-unit premise of that
statement: an arbitrary field, explicit integer valuation, affine group scheme
and supplied `IntegerValuationBuildingData`. The conclusion concerns the original
ordinary affine roots and original actual normalizer action on the same reduced
apartment.

The proof assembles the additive integer-valuation helpers. The actual rank-one
factorization theorem supplies all opposite factor pairs. From
`IntegerRootReflections` and `IntegerAffineRootArrangement`, the ordinary affine
roots have finite spanning derivatives, are nonconstant, and have coroots whose
reflections preserve the ordinary roots. The integral actual pair coroots and
finite spanning uniqueness give the integral pairing axiom for every coroot.

`IntegerAffineRootLocalFiniteness` uses rational-character denominators, the
actual centralizer correction between same-root reflections and full supplied
V6 to prove bounded finiteness at an apartment point. To obtain the bounded
same-derivative-difference clause of AR4, choose a point `x`. If
`|θ(y) - ψ(y)| ≤ M` for every `y`, the triangle inequality gives
`|θ(x)| ≤ M + |ψ(x)|`. The desired set is therefore a subset of the finite
bounded set already proved.

The published `IntegerAffineRootFibreInfinitude` supplies the other clause of
corrected AR4. An actual integral coroot evaluated at the supplied order-one unit
has centralizer translation of root value `-2`. Its inverse normalizer action
adds the constant `2` to each affine root with that derivative, yielding an
infinite derivative fibre. This is the only step that uses the order-one-unit
premise.

These fields construct
`IntegerValuationBuildingData.isAffineRootSystemWithRankZero_affineRoots`.
Derivative spanning includes rank zero without requiring a root to exist.
Finally, `IntegerValuationBuildingData.affineWeylGroup_le_range` realizes every
coroot reflection as the action of an actual opposite-pair normalizer element;
subgroup closure gives the exact second conjunct. The host theorem pairs these
two conclusions.

This is an internal assembly of the proved helper interfaces, following the
route already used by `ValuationAffineRootSystems` for local-field data.
The target's paired Markdown records its original KP §§6.2–6.3 correspondence
and corrections. The implementation adds no hypothesis and does not alter the
statement or its imported definitions. It uses no proof of a downstream chamber,
integral-twist or cocycle-vanishing statement.
