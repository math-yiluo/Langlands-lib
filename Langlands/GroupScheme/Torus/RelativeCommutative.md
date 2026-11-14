# Commutativity of tori over an arbitrary base

Worker 701, supporting Task 6384.

`RelativeTorus.IsTorus.isCommMonObj` proves that every actual group scheme
over an arbitrary scheme satisfying `RelativeTorus.IsTorus` has a
commutative group-object structure. No field, connectedness or affineness
assumption on the base is imposed.

The helper `isCommMonObj_of_etaleCover` proves that commutativity of an
actual group scheme descends from an étale covering family of its base.
For each test scheme, pull back the cover to that test scheme. The
base-change point equivalence identifies the restricted points with
points of each pulled-back group scheme and preserves multiplication.
Thus the two products agree after every member of the pulled-back
cover. Subcanonicity follows by comparison with Mathlib's subcanonical
fppf topology, since every étale morphism is flat and locally of finite
presentation. This makes the covering family
jointly epimorphic for morphisms of schemes, so the original products
agree. The all-test commutativity characterization then supplies
`IsCommMonObj`.

The torus theorem applies this helper to the étale splitting cover in
the definition of `RelativeTorus.IsTorus`, using the published theorem
`IsSplitTorus.isCommMonObj` on each member. It is an internal
consequence of the published torus definition and split-torus
commutativity, rather than a new geometric structure theorem.

`RelativeTorus.IsTorus.commGroupScheme` bundles the torus, with its given
underlying scheme and group laws, as an object of `CommGroupScheme S`.
`commGroupScheme_toGrp` records that forgetting commutativity gives back
the original group scheme. This definition uses the proved commutativity
structure and changes no scheme or morphism.

Shared declarations `IsTorus.isCommMonObj`, `IsTorus.commGroupScheme`, `IsTorus.commGroupScheme_toGrp` are imported from `Langlands.GroupScheme.Torus.RelativeCommutativity`; their mathematical hypotheses, conclusions and data are unchanged.
