# Dense cells of actual local-isogeny graphs

This derived support module adapts `SplitLeviGluingGraphDensity` to
`SimpleIsogenyGraph i i' t`, whose source and target tori may differ and whose
local maps may have characteristic-power root factors. It reuses the abstract
three-factor word and closure-action theorems from
`SplitLeviGluingRationalDensity`, source generation from
`SplitIsogenySourceGeneration`, and all-test commutation from
`SplitIsogenyMixedRoots`.

For a supplied graph `D`, `positiveRational` and `negativeRational` are the
actual rational ranges of its paired source-simple root lifts, and
`torusRational` is the rational range of its distinguished source-torus lift.
`positiveGenerated` and `negativeGenerated` are the abstract subgroups generated
by those respective ranges. `rationalGraphCell` is the literal set product
negative-generated times torus-range times positive-generated. These definitions
do not assert that either generated subgroup already represents an entire
algebraic dynamic factor.

Each generated subgroup lies in the corresponding graph dynamic unipotent
functor on rational points. The torus normalizes both, by its proved
normalization of every root lift and the normalizer-of-closure lemma.
`rootFamilyRationalPoints_eq_closure` rewrites the actual family-generated
subgroup as the closure of the positive ranges, negative-generated subgroup,
and torus range, in the form needed by the abstract word theorem. The torus
term remains present even when the simple-root index is empty.

The closure action and `dense_rationalGraphCell` assume that the field is
algebraically closed, the source is connected, its torus inclusion is closed,
and the ambient generic-chamber dynamic centralizer equals that torus range.
They also use actual source and target root data, finite root indices and
lattices, reducedness of both data, a split target torus, a root-datum isogeny
`f : RootDatumIsogeny p P' P`, and the prescribed character-map equation
`t ≫ χ = f.weightMap χ`. The groups are smooth affine over the field.
The source split torus and generic chamber are part of `D`.

`rationalGraphCellClosureAction` applies the abstract left-multiplication action
on rational-point closure. Its inputs are the proved normalization statements,
distinct-index graph commutation, and equal-index local-cell closure. The same
inputs and density of the family-generated rational subgroup prove
`dense_rationalGraphCell`. Thus the locations of this actual three-factor
rational cell are Zariski dense in the graph. This density is a conclusion,
not an input to the construction.

`DenseSimpleIsogenyGraph` stores the supplied graph and that density certificate.
`denseSimpleIsogenyGraph` proves its certificate from source connected
reductivity and a maximal source torus, using the generic-chamber centralizer
identity to discharge the explicit centralizer hypothesis. The isogeny
parameter `p` is arbitrary in this support lemma; in the host realization it
is the field characteristic exponent. No root factors are replaced by one.

This module does not prove target simple-system transport, fullness of the
closed dynamic factors, graph-torus maximality, either projection being an
isomorphism, or the general realization and fixed-torus extension theorem.
