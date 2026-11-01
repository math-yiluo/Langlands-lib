# The actual disconnected CM polarized tower presheaf

This extends the existing conditional connected-base CM polarized tower by a
product over actual connected component schemes. The source prescription is
Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), III.1, printed pp. 90–91, PDF pp. 98–99. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 90 defines the value on a disconnected locally Noetherian base as the
product of the values on its connected components; page 91 gives the
pointed definition and canonical independence from the geometric point.

The construction imports the existing unpointed presheaf and the actual open
component-scheme construction. `componentCMOver` restricts the original map to
`Spec F` along the actual component inclusion. `ComponentwiseAdmissibleCMBase`
requires a locally Noetherian original scheme and the existing named
`AdmissibleCMBase` prerequisites on every actual component scheme. Its full
subcategory retains every actual morphism over `Spec F`. There is no flatness
restriction and no supplied output scheme or arbitrary component family.

The arithmetic inputs are the existing universe-zero number fields and central
simple unitary datum, with the same normalized Harris CM section and reflex
structure. The prerequisites remain explicit: the existing tensor and Picard propositions,
duality and polarization stability, finite Weil transition, adelic comparison
and torsion finiteness statements are unchanged. On each actual component,
admissibility requires connectedness, local Noetherianity, quasi-separatedness,
torsion units, finite étale roots of unity, Lie base-change naturality, positive
pair additivity and existence of constrained dual data for every actual abelian
scheme. The component geometry proves connectedness and local Noetherianity; Mathlib
derives quasi-separatedness from local Noetherianity. This
module does not prove the remaining named inputs for all locally Noetherian
CM bases.

At a Harris level `U`, `disconnectedClassTower X` is the dependent product
of `unpointedClassTower (componentCMBase X c)` over the actual quotient
`ConnectedComponents X.obj.left`. Every original Harris level and Hecke
transporter acts component by component. These are the same normalized joint
classes on the same representatives as the connected construction; no change
to its dimension or Lie normalization is made.

For an actual map `f : Y ⟶ X`, the pullback at a component `c` of `Y` selects
the factor indexed by the actual image component of `c` in `X`, then applies
the existing connected pullback along the actual restricted component morphism.
`componentCMBaseHomTo` proves the triangle over `Spec F`. Its identity and
composition laws follow from the component-scheme laws.

`disconnectedClassTowerPullback_app_eq` states the exact value for any equal
specification of the image component. This avoids dependence on an equality
transport convention. The existing connected pullback identity and composition,
together with the actual component map laws, prove disconnected identity and
composition. They assemble `disconnectedClassTowerPresheaf`, a presheaf of
functors on the full original Harris level category.

For a preconnected base, evaluation at any component is an isomorphism of
towers, using uniqueness of the actual component index. If the original base
also satisfies the named connected admissibility conditions,
`disconnectedClassTowerConnectedIso` identifies the result with the original
connected tower. Its second factor is the existing presheaf's image of the
inverse of the actual component inclusion isomorphism over `Spec F`.
For an empty base, `disconnectedClassTowerEmptyUnique` constructs the unique
empty-product value at every level.

The product prescription is from Harris–Taylor; the categorical assembly and
its intrinsic proofs are derived here from the imported constructions. The
source representability assertion on page 91 is not proved by this module.
Representability of the precise actual moduli functor, representing scheme
levels, finite étale level maps and coefficient descent remain further
obligations of the host task.
