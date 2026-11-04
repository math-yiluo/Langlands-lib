# Generic-fiber adelic points of specified arithmetic pullback cones

`Langlands.Global.AdelicSpreadModelPullbackStatement` conjoins the
function-field and number-field statements that the actual adelic point
comparison of the generic fiber of a specified arithmetic pullback cone is a
homeomorphism. All types share arbitrary universe `u`.

The data are finite-type arithmetic models `X`, `Y` and `Z` over the actual
outside-`S` integer ring, morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, and any
relative pullback cone `c` with its categorical limit proof. Here finite type
means locally finite type and quasi-compact. Only the structure morphism of
`Z` is required to be separated. The factors may be nonaffine and
nonseparated. The functor `G` is the actual pullback along the inclusion of
the integer ring into the original field. Its image cone is a field-scheme
pullback because the pullback functor preserves limits.

The source is the actual full-adele point set of `G.obj c.pt`, and the target
is the subtype of compatible pairs in the product of the actual full-adele
point sets of `G.obj X` and `G.obj Y`. Compatibility is equality of the actual
relative scheme morphisms after postcomposition with `G.map f` and
`G.map g`. The comparison is the existing
`affineSchemePullbackPointComparison` applied to `c.map G`; its definition
uses no affineness assumption. It sends a point to its composites with the
two generic-fiber cone legs.

Each point space has precisely the existing spread topology from its
original model and the identity generic-fiber isomorphism. The target uses
the product topology followed by the subtype topology; the source topology
is independently the transported final arithmetic topology. The comparison
does not define either topology.

In the function-field clause, the constant field `k` is perfect, and `F`
retains its specified `k` and `RatFunc k` actions and compatible scalar
tower. `FunctionField k F` imposes finiteness over the rational-function
field, without a separability premise. There is no finiteness premise on
`k`. The perfectness premise is inherited from the existing actual
function-field generic-fiber point construction. The number-field clause
uses `Adeles K`, including all infinite factors. The initial finite set `S`
may be empty in both clauses. No local compactness or residue-field
finiteness assumption occurs.

This is a derived comparison associated with Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.8–9: the paragraph following Theorem 3.6, and Section 4's construction of
the generic-fiber adelic topology and its pullback discussion. Registered
source: `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The enlarged constant-field scope and nonseparated-factor scope are derived
extensions, not claims quoted verbatim from Conrad. The justification is
the fixed-model pullback theorem and the natural homeomorphisms between
actual model points and actual generic-fiber points. Their product
homeomorphism identifies the two compatible-pair subspaces, and naturality
identifies their cone-leg comparison maps.

This unit specifies a chosen arithmetic model cone. It assumes no descent
of an independently given field cone: such descent, eventual separatedness
of a base model, and comparison with arbitrary independently chosen spreads
remain distinct obligations of the whole-paper program. This file states
propositions only and supplies no proof or whole-task completion.
