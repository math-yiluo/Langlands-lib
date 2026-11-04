# Pullbacks of full-adele points of fixed arithmetic models

`Langlands.Global.AdelicFixedModelPullbackStatement` states the pullback
homeomorphism for actual full-adele points of finite-type models X, Y and Z
over the actual outside-S integer ring, with Z separated over that ring.
The factors X and Y can be nonseparated and nonaffine. Finite type is expressed
as local finite type and quasi-compactness of each structure morphism.

For any relative morphisms f : X → Z and g : Y → Z, and any limiting
pullback cone c, the map sends p to its composites with c.fst and c.snd.
It is the already constructed `affineSchemePullbackPointComparison`, which
applies to arbitrary schemes despite its name. The target consists of pairs
whose composites into Z agree as actual relative scheme morphisms. It carries
the subspace topology from the product of the two existing fixed-model
full-adele point topologies. The source carries the existing final topology
on points of c.pt. The assertion is that this canonical comparison is a
homeomorphism.

The curve clause uses the actual curve-place adele ring and the specified
k → RatFunc k → F tower with `FunctionField k F`. Constants need not be finite
or perfect, and the extension need not be separable. The number-field clause
uses the full adele ring, retaining every infinite completion. The initial
finite set S may be empty in either case. Both clauses retain the original
integer-base scalar action through `curvePlaceAdeleOver` or
`numberFieldAdeleOver`. The common universe is arbitrary.

## Provenance and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, printed p.9, Section 4 opening discussion, explains the final adelic
topology using open arithmetic transition maps and asserts compatibility
with fiber products in its discussion of separated schemes. Printed p.8,
after Theorem 3.6, asserts the corresponding arithmetic-level compatibility.
Registered source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

This is a derived fixed-model form of the separated assertion. Its extension
to nonseparated X and Y, arbitrary curve constants, inseparable extensions
and empty S is supported by the following argument. Finite-type arithmetic
stage maps for X and Y are continuous and open, and jointly cover their
full-adele points. Pairs of points lift to one common enlarged stage.
Separatedness of Z makes its stage-to-full point map injective, so a pair
is compatible over the full adeles exactly when its two stage lifts are
compatible. Restricting the product open maps to these compatible-pair
subspaces gives a jointly surjective family of continuous open maps.
The arithmetic-level pullback homeomorphisms then establish continuity
of the inverse full-adele comparison. This argument uses neither compactness
nor finiteness of residue fields.

The separated-base formulation includes products by taking Z to be the
terminal model. This unit supplies a proposition target; its proof and
the comparison with generic-fiber adelic point topologies are separate
obligations.
