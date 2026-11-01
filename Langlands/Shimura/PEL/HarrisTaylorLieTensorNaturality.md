# Actual actions and rational naturality of Harris–Taylor Lie tensor factors

Let `L` be an imaginary quadratic CM number field, let `K` be a number
field containing `L`, and let `s : S ⟶ Spec K` be an actual structure
morphism. Let `B` be an abelian scheme over `S` and let
`i : A →ₐ[ℚ] End0 B` be a rational action of a `K`-algebra `A`.
The two actual sheaves `lieTensorSheaf L s B i conjugate` have sections
`Γ(B.Lie,U) ⊗_(Γ(S,U) ⊗_ℚ L) Γ(S,U)`. The flag `false` selects the
structural imaginary-field embedding and `true` its CM conjugate.
Their section modules, canonical restrictions, sheaf condition, full
Lie eigensheaf comparisons and canonical projections are constructed in
`HarrisTaylorLieTensorFactor`.

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.89–90 / PDF pp.97–98,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source's imaginary field `E` is `L` here and its CM field `F` is `K`.
The source defines the two tensor factors of the actual Lie sheaf and
then imposes compatibility on the positive factor. This module provides
derived action and naturality constructions on those factors, using
the actual differentiated algebra action and rational differentials.

`lieTensorAction` is a ring homomorphism from the full algebra `A` to
endomorphisms of either tensor sheaf. It conjugates the constructed
`lieEigensheafAction` by `lieTensorSheafIso`. The unit and zero laws use
the inverse identities, multiplication additionally uses the convention
`End.mul f g = g ≫ f`, and addition uses bilinearity of composition in
the preadditive category of actual module sheaves. The comparison
isomorphism intertwines this action with the eigensheaf action.
`lieTensorProjection_intertwines` follows from the corresponding
Lie eigenprojection identity after composing with the inverse tensor
comparison. Product extensionality then proves
`lieTensorSplitting_intertwines` for the full two-factor splitting.

For a second actual abelian scheme `B'` with action `i'`, let
`f : Hom0 B B'` be an actual rational homomorphism satisfying the
full algebra intertwining equation for every `a : A`.
`lieTensorMap` conjugates the constructed restriction of its actual
rational differential by the two tensor comparisons. The comparison
identity and `lieTensorProjection_naturality` are proved using the inverse
identities and the corresponding eigensheaf statements. Thus the canonical
projections `m ↦ m ⊗ 1` commute with the actual rational differential.
`lieTensorMap_intertwines` proves that this map intertwines the full
algebra actions on the two tensor sheaves. The tensor map preserves
identity and composition; for composition the proof conjugates the
explicit eigensheaf composition theorem and cancels the intermediate
inverse comparisons. Product extensionality proves naturality of the
actual Lie splitting.

Finally `lieTensorIso` composes the two tensor comparisons with the
constructed eigensheaf isomorphism arising from an actual equivariant
isomorphism in the rationalized abelian-scheme category. Its forward map
is proved to be the corresponding `lieTensorMap`. Neither an output
sheaf, an output map, nor any comparison identity is supplied as an input.
These constructions assert no local freeness, prescribed rank, equality
of the two totally real field actions, arbitrary scheme pullback, or
representing PEL schemes. Those remain separate geometric obligations.
