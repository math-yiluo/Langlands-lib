# Ampleness under an actual module-sheaf isomorphism

This module proves the Library proposition
`Langlands.AlgebraicGeometry.Picard.AmpleIsoStatement`: for every scheme `X`
and line bundles `L M : LineBundle X`, an isomorphism `L.obj ≅ M.obj` of the
underlying module sheaves carries ampleness of `L` to ampleness of `M`.
The statement and all definitions come from the Library unchanged. The proof
uses only those definitions; no external literature result is involved.

## Transport of trivialization opens

- `Langlands.SchemeModule.trivializesOn_mapIso_iff`: for arbitrary module
  sheaves `P Q : X.Modules`, an isomorphism `e : P ≅ Q`, a global section
  `s : GlobalSections P` and an open `U`,
  `TrivializesOn Q (e.hom.app ⊤ s) U ↔ TrivializesOn P s U`.

  Proof. Unfold `TrivializesOn`. The published
  `Langlands.SchemeModule.sectionHom_naturality` (from
  `Langlands.AlgebraicGeometry.Modules.TensorSections`) rewrites the
  morphism of the image section as `sectionHom P s ≫ e.hom`. The restriction
  functor sends this composite to the composite of the restrictions, and
  composing with the restricted isomorphism `e.hom` does not change whether
  a morphism is an isomorphism (`isIso_comp_right_iff`).

- `Langlands.SchemeModule.trivializationOpen_mapIso`: with the same data,
  `trivializationOpen Q (e.hom.app ⊤ s) = trivializationOpen P s`.

  Proof. Both sides are suprema of the opens on which the section
  trivializes. By the previous lemma the two families of opens are equal,
  so the suprema are equal. This is equality of the whole maximal opens,
  with no hypothesis on `P` or `Q`.

## Ampleness transport

- `Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple.of_iso`: if
  `hL : L.IsAmple` and `e : L.obj ≅ M.obj`, then `M.IsAmple`.

  Proof. The compactness part of ampleness is unchanged. Given a point `x`,
  ampleness of `L` gives an exponent `n ≥ 1` and a section `s` of the actual
  tensor power `tensorPow L.obj n` whose section open contains `x` and is
  affine. The published `Langlands.Scheme.Modules.tensorPowIso e n`
  (from `Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms`) is an
  isomorphism `tensorPow L.obj n ≅ tensorPow M.obj n` of the actual tensor
  powers. Since `sectionOpen` is the trivialization open of the tensor power,
  `trivializationOpen_mapIso` shows that the image section has the same section
  open. So the same exponent `n` and the image section witness ampleness of
  `M` at `x`, with both point membership and affineness.

- `Langlands.AlgebraicGeometry.Picard.ampleIso : AmpleIsoStatement.{u}`
  applies `IsAmple.of_iso` to the given isomorphism.
