# Affine and global-section point coordinates

This internal construction compares the two point equivalences for a
functor `F : CommAlgCat R ⥤ GrpCat` with a specified corepresentation by a
commutative `R`-algebra `B`. Here `R` is any commutative ring, and the
algebras, groups and schemes use the same universe. No field, finite-type
or smoothness hypothesis is imposed.

For a commutative `R`-algebra `S`, let `T = algSpec R (op S)` and let
`Γ_R(T)` denote its relative global-section algebra. The definition
`affineSectionsIso S` constructs an isomorphism

\[
  q_S : \Gamma_R(\operatorname{Spec}_R S) \simeq S
\]

in `CommAlgCat R`. It takes the counit of Mathlib's actual relative
adjunction `algΓAlgSpecAdjunction R`, removes the opposite category and
reverses the resulting isomorphism. The counit is invertible because the
right adjoint `algSpec R` is fully faithful. Thus this is a constructed
isomorphism, not an additional input. `affineSectionsAlgEquiv` gives the
same isomorphism as an `R`-algebra equivalence.

`affineSectionsIso_inv` records that `q_S` inverse is the counit with
opposites removed. `affineSectionsIso_inv_ringHom` identifies its underlying
ring map with `(Scheme.ΓSpecIso S).inv`; this follows by unfolding the
relative adjunction. `affineSectionsIso_hom_ringHom` identifies the forward
ring map with `(Scheme.ΓSpecIso S).hom`. Its proof compares the two inverse
identities and uses injectivity of the latter isomorphism's inverse.
These normalizations retain the actual structural `R`-algebra action.

The inverse is natural. For every `R`-algebra map `f : S → T`,
`affineSectionsIso_inv_naturality` proves

\[
  \Gamma_R(\operatorname{Spec} f)\circ q_S^{-1}
    = q_T^{-1}\circ f.
\]

This is the counit's naturality identity with opposites removed.

Let `G` be the affine group scheme constructed from the corepresentation.
For every actual point `x : Spec_R S → G`, the theorem
`pointsEquiv_eq_affinePointsEquiv` proves

\[
  \operatorname{pointsEquiv}(x)
    = F(q_S^{-1})(\operatorname{affinePointsEquiv}(x)).
\]

The left side lies in `F(Γ_R(Spec_R S))`; the affine coordinate on the right
lies in `F(S)` before applying `F(q_S inverse)`. The proof expands both
coordinate equivalences. Naturality of the adjunction counit expresses
the inverse adjunction map of `x` as the counit followed by the algebra
map recovered by full faithfulness. The corepresentation's composition
law then gives the displayed equality. Finally,
`map_affineSectionsIso_pointsEquiv` proves the converse coordinate formula

\[
  F(q_S)(\operatorname{pointsEquiv}(x))
    = \operatorname{affinePointsEquiv}(x),
\]

using functoriality and the inverse identity for `q_S`.

The provenance is the existing `Corepresented` and `CorepresentedPoints`
constructions, Mathlib's relative adjunction, and its fully faithful right
adjoint theorem. This is a reusable coordinate comparison for the Harris
scalar-extension and matrix calculations. It does not yet identify the
Harris iterated-model matrices with the direct rational-group coordinates
or establish a reflex-field conjugacy statement.
