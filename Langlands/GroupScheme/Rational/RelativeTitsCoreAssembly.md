# The relative Tits system from seven structural statements

This internal auxiliary module supports the proof task for
`Langlands.GroupScheme.RelativeTitsSystemStatement`. It shortens the published reduction
`relativeTitsSystemStatement_of_structuralStatements` (module
`Langlands.GroupScheme.Rational.SimpleRootParabolicFactorization`) from nine inputs to seven.
The root-subgroup realization and vector statements are no longer inputs.

`relativeTitsSystemStatement_of_coreStatements` proves `RelativeTitsSystemStatement.{u}` from
the following published statements:

- `RelativeWeylCoxeterStatement`;
- `StandardParabolicEndpointsStatement`;
- `RationalBruhatStatement`;
- `RootRankOneFactorizationStatement`;
- `RelativeRootSystemStatement`;
- `GenericCentralizerStatement`;
- `RelativeRoot.DynamicRootOrderedProductStatement`.

None of these inputs is proved here, so the module does not prove the target. It adds no
axioms.

## Nonidentity simple-root points

`RelativeSimpleRootPointData.ofActual hT i ν` assumes `[IsAffineHom G.X.hom]`,
`[Smooth G.X.hom]`, a split torus `hT : IsSplitTorus T.toGrp`, a homomorphism
`i : T.toGrp ⟶ G` and a cocharacter `ν`. It is a structure `RelativeSimpleRootPointData i ν`
(module `RelativeTitsNondegeneracy`). For every simple relative root `a`, its point is a
`k`-point of `RelativeRoot.subgroup i a` other than `1`, and the proofs of the `mem` and `ne_one`
fields come with it. The point is chosen by `Classical.choose` from the published
`RelativeRoot.exists_rootPoint_actual` (module `RootSubgroupRationalNontrivial`). That result
gives such a point for every actual relative root of a smooth affine group with a split torus
action, over any field. A simple root is a relative root through `a.property.1.1`: simple roots
are positive roots, and positive roots are relative roots.

The published constructor `RelativeSimpleRootPointData.of_rootSubgroup_statements` gives the
same kind of data from the realization and vector statements. This constructor needs neither.

## The assembly

`relativeTitsSystemStatement_of_coreStatements` applies the published
`relativeTitsSystemStatement_of_rootProduct`. That result takes the seven inputs above and the
nondegeneracy field `conj_not_le` for all data, as its hypothesis `hconj`. Fix a field `k`, a
connected reductive group `G` (`hG`), a maximal split torus `i` (`hi`) and a cocharacter `ν`.
The proof takes `IsAffineHom` and `Smooth` from `hG.isAffineHom` and `hG.smooth`, and the
monomorphism instance from `hi.isSplitSubtorus.mono`. Then `hconj` is the published
`RelativeSimpleRootPointData.conj_not_le`, applied to `RelativeSimpleRootPointData.ofActual`
with the split torus `hi.isSplitSubtorus.1`. The hypothesis that `ν` is generic is not used
for this field.

## Provenance

Both declarations are internal and derived, and neither has a separate literature source. They
compose published Library results:

- `relativeTitsSystemStatement_of_rootProduct` (`SimpleRootParabolicFactorization`);
- `RelativeSimpleRootPointData.conj_not_le` (`RelativeTitsNondegeneracy`);
- `RelativeRoot.exists_rootPoint_actual` (`RootSubgroupRationalNontrivial`).

The nondegeneracy argument itself is the published one in `RelativeTitsNondegeneracy`. For a
simple root `a` and a representative `n` of its reflection, `n` conjugates a nonidentity point
of `U_a(k)` into `U_{-a}(k)`, and that conjugate does not lie in `P_∅(k)`. This module only
supplies the nonidentity points.
