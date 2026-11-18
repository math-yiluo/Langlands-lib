# Homomorphisms to the additive group and primitive coordinate functions

Module `Langlands.GroupScheme.Torus.MultiplicativeTypeAdditiveHom`, namespace
`Langlands.GroupScheme.MultiplicativeTypeCharacterization`. Author: Worker 894.

Internal helper module for the proof of
`Langlands.GroupScheme.MultiplicativeTypeCharacterizationStatement`. For an affine group
scheme `G` over `Spec k` (`k` a field, `[IsAffine G.X.left]`), with coordinate Hopf algebra
`AffineCoordinates.hopfAlgebra G`, it proves that every homomorphism
`G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1` (that is, `G → 𝔾ₐ`) is trivial if and
only if every primitive element of the coordinate Hopf algebra is `0`. This is the
standard correspondence between homomorphisms to `𝔾ₐ` and primitive elements, used in
Milne, *Algebraic Groups* (2017), proof of Theorem 12.18 (registered source
`milne-2017-algebraic-groups`, printed pp. 237–238). The module adds one helper
definition and no new structural assertion.

## Declarations

- `eq_zero_of_isPrimitiveElem_of_subsingleton`: if
  `Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)`, every primitive
  element `a` of `AffineCoordinates.hopfAlgebra G` is `0`.
- `gaCoord B x` (helper `abbrev`): for a commutative `k`-algebra `B` and a point
  `x : (Spec B).asOver (Spec k) ⟶ 𝔾ₐ.X`, the coordinate of `x`
  (`VectorGroup.coordinates`, index `0`), transported from global sections of `Spec B` to
  `B` by `Scheme.ΓSpecIso`.
- `coordinatePointEquiv_eq_comp`: the Library point `AffineCoordinates.coordinatePointEquiv
  G B (toConv χ)` attached to an algebra map `χ` is `Spec.map χ` (as a morphism over
  `Spec k`) followed by the underlying morphism of `AffineCoordinates.hopfSpecIso G`. This
  holds by definition (`rfl`).
- `gaCoord_mul`: `gaCoord B (x * y) = gaCoord B x + gaCoord B y`.
- `includeLeft_mul_includeRight`: for a commutative `k`-bialgebra `A`, the convolution
  product of the two inclusions `A → A ⊗[k] A` is `Bialgebra.comulAlgHom k A`.
- `hom_eq_one_of_noPrimitive`: if every primitive element of the coordinate Hopf algebra
  is `0`, then every `q : G ⟶ 𝔾ₐ` has `q.hom.hom = 1`, the identity point.
- `subsingleton_of_noPrimitive`: under the same hypothesis,
  `Subsingleton (G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)`.

## Proofs

**Nonzero primitive elements give nonzero homomorphisms.** Suppose `a ≠ 0` is primitive.
The Library lemma `AffineCoordinates.isPrimitiveFunction_of_isPrimitiveElem` shows that
`a` is additive on all algebra-valued points of the corepresented coordinate functor, so
the one-element family `fun _ : Fin 1 => a` satisfies `VectorGroup.IsPrimitiveFamily` for
`AffineCoordinates.corepresentation G`. The Library's `VectorGroup.quotientMap` of this
family is nonzero by `Unipotent.quotientMap_ne_zero`. Composing it with the inverse of
`AffineCoordinates.groupSchemeIso G` gives a homomorphism `G ⟶ 𝔾ₐ`; if it were `0`, so
would be `quotientMap` (cancel the isomorphism, `Limits.comp_zero`). This contradicts the
subsingleton hypothesis, which forces it to equal `0`.

**Homomorphisms give primitive elements.** Let `A` be the coordinate Hopf algebra and
`E` the underlying morphism of `AffineCoordinates.hopfSpecIso G`, an isomorphism from
`(Spec A).asOver (Spec k)` to `G.X`. Put `u = E ≫ q.hom.hom` and `a = gaCoord A u`.
For every `χ : A →ₐ[k] B`, the point `coordinatePointEquiv G B (toConv χ) ≫ q.hom.hom`
equals `Spec.map χ ≫ u`, so `VectorGroup.coordinates_comp` and the Library's
`HopfPrimitive.appTop_specMap_inv` give `gaCoord B (…) = χ a`. Now take `B = A ⊗[k] A`
and the two inclusions. `coordinatePointEquiv` is multiplicative (a `MulEquiv`), `q.hom.hom`
is a monoid morphism (`MonObj.mul_comp`), coordinates of products add (`gaCoord_mul`), and
the convolution product of the inclusions is `comulAlgHom` (`includeLeft_mul_includeRight`,
proved by `AlgHom.convMul_apply` and `simp`, which applies Mathlib's simp lemma
`Algebra.TensorProduct.lift_includeLeft_includeRight`).
Hence `Δ a = a ⊗ 1 + 1 ⊗ a`, so `a` is primitive and therefore `0`. Then all coordinates of
`u` vanish (`VectorGroup.points_ext`), so `u = 1`, and
`q.hom.hom = E⁻¹ ≫ u = E⁻¹ ≫ 1 = 1` (`MonObj.comp_one`). Two homomorphisms with the same
underlying morphism are equal (`Grp.hom_ext`), which gives `subsingleton_of_noPrimitive`.

## Provenance

Internal derivation from the published Library interfaces named above
(`AffineCoordinates.hopfAlgebra`, `hopfSpecIso`, `coordinatePointEquiv`,
`corepresentation`, `groupSchemeIso`, `VectorGroup`, `HopfPrimitive.appTop_specMap_inv`,
`Unipotent.quotientMap_ne_zero`) and Mathlib. The mathematical content is Milne's remark
in the proof of Theorem 12.18 that homomorphisms `G → 𝔾ₐ` correspond to primitive
elements of `O(G)`; Milne states it for algebraic groups, and here only affineness over the
field is used.
