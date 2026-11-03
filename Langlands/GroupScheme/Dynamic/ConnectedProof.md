# Connectedness of dynamic subgroups of a smooth affine group over a field

This module proves `Langlands.GroupScheme.DynamicConnectedStatement` (module
[`SmoothConnectedStatement`](SmoothConnectedStatement.md)). Let `k` be a field, `G` a group scheme
over `Spec k` whose structure morphism is smooth and affine, `χ : 𝔾_m ⟶ G` a cocharacter (the
trivial one included) and `j : H ⟶ G` a homomorphism of group schemes over `Spec k`. Then:

* if `j` represents `Dynamic.unipotent χ`, the underlying space of `H` is connected;
* if the underlying space of `G` is connected and `j` represents `Dynamic.parabolic χ` or
  `Dynamic.centralizer χ`, the underlying space of `H` is connected.

All declarations are in the namespace `Langlands.GroupScheme.DynamicConnected`, except the final
theorem `Langlands.GroupScheme.dynamicConnected`.

## The unipotent subgroup

`connectedSpace_of_isRepresentedBy_unipotent`, proved in the module
[`UnipotentConnected`](UnipotentConnected.md) by an algebraic contraction of the coordinate ring
of `U_G(χ)` (CGP, Proposition 2.1.8(4), end of Step 3, printed p. 56), gives the first assertion
for every affine `G` over a field.

## The parabolic and the centralizer: the open cell

This follows CGP, Proposition 2.1.8(4), end of Step 3 (printed p. 56): if `G` is connected it is
irreducible, so the open cell `U_G(−λ) × P_G(λ)` is connected, hence so is `P_G(λ)`, and
`Z_G(λ)` is its image under the limit map.

* `surjective_of_section`: a morphism of schemes with a section is surjective on points.
* `connectedSpace_of_section`: if a homomorphism of group schemes `f : H ⟶ H'` has a section and
  `H` is connected, then `H'` is connected (continuous image under a surjection).
* `irreducibleSpace_of_smooth`: a smooth group scheme over a field with connected underlying space
  is irreducible. It is locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`), hence
  integral by the published `CharacterLatticeProof.isIntegral_of_smooth`.
* `connectedSpace_of_isOpenImmersion`: a nonempty scheme with an open immersion into an
  irreducible scheme is connected (an open subset of an irreducible space is preirreducible,
  hence preconnected; an open embedding identifies the source with its image).
* `connectedSpace_of_isRepresentedBy_parabolic`: let `U⁻` be the published representative
  `Dynamic.Affine.unipotentScheme χ⁻¹` of the unipotent subgroup of the opposite cocharacter
  `χ⁻¹ = CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ`. The published theorem
  `oppositeCellStatement : OppositeCellStatement` (module
  [`Absolute.OppositeCellProof`](../Absolute/OppositeCellProof.md)), applied to `U⁻` and `j`,
  says that multiplication `U⁻ ×_k H → G` is an open immersion. The product is
  nonempty (it has the identity point over `Spec k`), so it is connected. The projection to `H`
  has the section `h ↦ (1, h)` (`surjective_of_section`), so `H` is connected.
* `connectedSpace_of_isRepresentedBy_centralizer`: the published limit homomorphism
  `Dynamic.limitGroupHom` from the explicit representative `Dynamic.Affine.parabolicScheme χ` to
  `H` has the section `Dynamic.centralizerToParabolic`
  (`centralizerToParabolic_comp_limitGroupHom`; `G` is separated since it is affine). The source
  is connected by the previous item, so `H` is connected (`connectedSpace_of_section`).

## Final theorem

`dynamicConnected : DynamicConnectedStatement.{u}` combines the three cases: the unipotent case
needs no connectedness of `G`, and the parabolic and centralizer cases use the connectedness
hypothesis of the target.

## Provenance and scope

Source: Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 2.1.8(4) and the end of Step 3 of its
proof (printed pp. 53, 56; PDF pp. 79, 82). The provenance of the unipotent case is recorded in
[`UnipotentConnected`](UnipotentConnected.md). No hypotheses beyond those of the target statement
are added in the final theorem.
