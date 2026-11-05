# The full maximal-torus preimage in a simply connected derived cover

Author: Worker 1554.

`DerivedCoverMaximalTorusPreimageStatement.{u}` is a proposition definition.
It states a structural input for the existing
`DerivedCoverTorusProductSmoothStatement.{u}` and contains no proof of that input.

For every field `k : Type u`, take actual group schemes `H`, `D`, `C` over
`Spec k`, an actual commutative group scheme `T`, and homomorphisms
`d : D → H`, `π : C → D`, `i : T → H`. The hypotheses are precisely
`IsSimplyConnectedDerivedCover d π` and `IsMaximalTorus i`, with their existing
published meanings. The conclusion is

```lean
IsTorus (subgroupIntersection (π ≫ d) i)
```

The intersection is the categorical pullback in group schemes of
`π ≫ d : C → H` and `i : T → H`. Its underlying scheme is the full
scheme-theoretic fiber product `C ×_H T`, including any nonreduced structure.
The conclusion uses the existing field-group predicate `IsTorus`. It asserts
that this actual group becomes a finite product of multiplicative groups
after a field extension. It does not replace the pullback by its reduced
subscheme, its identity component, its geometric points, or a torus mapping
isogenously onto its image.

The universe and field are unrestricted, including imperfect fields and
positive characteristic. No smoothness or étaleness of the central cover is
assumed. In particular, the finite central kernel itself may be nonsmooth.
No maximality assertion about the pullback inclusion is part of this
statement; being a torus is the structural conclusion needed here.

The provenance is internal: this isolates one prospective structural step
already described in the paired Markdown for the published
`SimplyConnected.DerivedCoverTorusProductSmoothStatement`. The mathematical
route is that the intersection of a maximal torus with the derived subgroup
is a maximal torus there, and its full inverse image under the central cover
is a maximal torus of `C`. Those assertions must be proved before they can
justify this statement. The existing `CentralIsogeny.TorusLift` theorem only
constructs a closed source torus mapping isogenously onto a target torus; it
does not identify the full inverse image required here.

A proof of this proposition would supply smoothness of the pullback through
the published `IsTorus.smooth` theorem. Scheme surjectivity of the product
map and its subsequent smoothness argument remain separate obligations.
