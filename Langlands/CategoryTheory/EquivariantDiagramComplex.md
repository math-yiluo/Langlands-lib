# Complexes of varying-group equivariant diagrams

This internal construction interchanges the degree and diagram-index axes.
Fix an actual group functor `D : I ⥤ GrpCat`, a preadditive coefficient category
`C`, and an arbitrary `c : ComplexShape ι`. The group, index object/morphism,
coefficient object/morphism and degree universes are independent.

`complexToDiagram c` turns a complex of `EquivariantDiagram D C` into a varying-group
diagram of actual Mathlib homological complexes. At index `i` and degree `n`
the coefficient object is `(K.X n).obj.obj i`, the differential is
`(K.d p q).hom.app i`, and the action is `(K.X n).ρ i`. The existing equivariance
of each differential gives its chain-map action, and transition equivariance
holds in every degree. A chain map is sent to its degreewise/indexwise component.

`diagramToComplex c` evaluates a diagram of complexes in every degree using
`mapFunctor` and uses `mapNatTrans` of Mathlib's differential natural
transformation for its differential. Shape and square-zero obligations follow
at each diagram index. Chain maps are evaluated degreewise.

`complexEquivalence c` packages these functors as inverse equivalences, with
identity components for the unit and counit. Their naturality equations are
proved by extensionality in degree and diagram index, reducing to the identity
laws in `C`. The triangle identity is proved by the same componentwise reduction.
Thus the equivalence retains the original coefficient objects, differentials,
group actions, transition maps and chain-map components while interchanging
their two axes.

The provenance is internal: the published `EquivariantDiagram`,
`EquivariantDiagramFunctor`, and `EquivariantDiagramPreadditive` modules supply
the objects, morphisms and additive structures; pinned Mathlib's
`Algebra.Homology.Additive` and `Algebra.Homology.Functor` supply actual complexes,
evaluation, differential natural transformations and the functor-of-complexes
construction. No assertion is attributed to Harris or Berkovich. No limits,
exactness, cohomology, geometric identification or smoothness is claimed.
