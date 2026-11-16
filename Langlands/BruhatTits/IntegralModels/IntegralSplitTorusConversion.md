# The supplied split integral torus as torus data of a component-model pair

Module `Langlands.BruhatTits.IntegralModels.IntegralSplitTorusConversion`.

This internal adapter works over an arbitrary domain `R` with fraction field
`K : Type u`. Let `G` be a group scheme over `K`, let `S` be a commutative group
scheme over `K`, let `i : S.toGrp ⟶ G`, and let `D` be supplied relative component
model data. A supplied `A : IntegralSplitTorusData D.neutral i` contains an
integral split torus of the neutral model with its actual inclusion and generic
commutative-group identification.

`IntegralSplitTorusData.toIntegralTorusData` regards these same data as
`IntegralTorusData D S i`. It keeps `A.torus` and `A.inclusion`, and uses
`underlyingTorusIso A.genericIso` as the generic group-scheme identification.
Its generic compatibility is precisely `A.generic_comm`. The four field lemmas
`toIntegralTorusData_torus`, `toIntegralTorusData_inclusion`,
`toIntegralTorusData_genericIso_hom` and `toIntegralTorusData_genericIso_inv`
are definitional equalities.

The definition and all four lemmas were moved verbatim from the published
`UnramifiedFacetSignDescent` module. Their Lean names, types and bodies are
unchanged; that module now imports this provider. The positive-root reduction
proof also imports this provider directly, because the adapter is its only
input from the former descent module. The new location depends only on the
integral torus interfaces and generic-group transport. No building descent,
coefficient descent, torus existence or extra mathematical conclusion is part
of this adapter.
