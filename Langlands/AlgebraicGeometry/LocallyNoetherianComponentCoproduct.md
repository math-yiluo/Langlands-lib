# Reconstruction from actual connected-component schemes

Author: Worker 57.

This derived geometric helper constructs the coproduct isomorphism from the
actual open connected-component schemes of a locally Noetherian scheme and
assembles arbitrary morphisms on those components. It uses the previously
proved open-component constructions and Mathlib's disjoint-open coproduct
criterion. Nilpotents are retained, since each component is the original open
restriction with its structure sheaf. No new literature assertion is used.

For `X : Scheme.{u}` with `IsLocallyNoetherian X`, the index is exactly
`ConnectedComponents X`. `componentCoproductIsColimit` applies
`AlgebraicGeometry.nonempty_isColimit_cofanMk_of` to the actual inclusions
`componentι X c`. Each is an open immersion. Their open ranges equal the
component opens, which cover `X` and are pairwise disjoint by
`componentOpen_iSup` and `componentOpen_disjoint`. Choosing the resulting
colimit witness proves invertibility of `Sigma.desc (componentι X)`.

`componentCoproductIso` is `asIso` of that identical coproduct map. Its forward
map is reflexively `Sigma.desc (componentι X)`. The theorem
`componentCoproductIso_ι` identifies its composite with each coproduct inclusion
with the original open-component inclusion.
`componentι_componentCoproductIso_inv` follows by the isomorphism inverse law
and identifies the original component inclusion followed by the inverse with
the corresponding coproduct inclusion.

For any scheme `Y` in the same universe and any family
`f c : componentScheme X c ⟶ Y`, `componentDesc X f` is literally the inverse
of `componentCoproductIso X` followed by `Sigma.desc f`.
`componentι_componentDesc` proves that restriction to each actual component
recovers exactly `f c`. The original component open cover proves
`component_hom_ext`, equality of morphisms whose component restrictions agree.
That equality criterion proves `componentDesc_restrict`, reconstruction of any
original morphism, and `componentDesc_comp`, compatibility with
postcomposition. Reassociated inclusion and composition equations are also
provided where marked in Lean.

Neither finiteness of the component set nor nonemptiness, quasi-compactness,
reducedness or flatness is assumed. The empty scheme therefore uses its actual
empty component index and coproduct. The result is geometric infrastructure
for extending actual connected-source constructions to locally Noetherian
sources; it supplies no representability or Shimura covering theorem.
