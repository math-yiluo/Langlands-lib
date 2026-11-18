# Tensor products of semisimple representations over an algebraically closed field

This module is internal supporting work for the proof of
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement`. It proves
Milne's Corollary 22.44 for rational-point representations of a smooth affine group over an
algebraically closed field of characteristic zero, taking Milne's Theorem 22.42 (published
statement `CharZeroReductiveSemisimpleRepresentationStatement`) as the explicit hypothesis `h22`.

## Lemmas on rational points and images

- `exists_rationalPoint_lift`: over an algebraically closed field `K`, a morphism `f : X ⟶ Y` of
  schemes over `Spec K` whose underlying morphism is surjective and locally of finite type is
  surjective on rational points. The fibre product of `f` with a rational point `y` is nonempty
  (Mathlib's `Scheme.Pullback.exists_preimage_pullback`) and locally of finite type over `Spec K`,
  so it has a rational point by the published `nonempty_rationalPoints`.
- `range_rationalRepresentation_restrict`: if `q : J ⟶ I` is surjective on rational points, then
  for every matrix representation `θ` of `I` the rational-point representations of
  `θ.restrict q` and `θ` have the same image.
- `kernelι_projection_comp_eq_zero`: for a matrix representation `φ` of an affine group `J`, a
  homomorphism `f : J ⟶ L` that kills every point killed by `φ` kills the full kernel of the
  projection `AffineHomImage.projection φ` onto the published scheme-theoretic image
  `AffineHomImage.image φ` (because `projection φ ≫ inclusion φ = φ`).

## Tensor products

`tensor_rationalRepresentation_isSemisimple h22 ρ σ hρ hσ`: let `K` be algebraically closed of
characteristic zero and `J` a group scheme over `Spec K` with `[Smooth J.X.hom]` and
`[IsAffineHom J.X.hom]`. If `ρ : MatrixRepresentation J (Fin n)` and
`σ : MatrixRepresentation J (Fin m)` have semisimple rational-point representations, so has
`ρ.tensor σ`.

Proof (Milne's argument: replace `G` by its image in `GL_V × GL_W`):

1. Let `φ = ρ.sum σ` (module `SumRepresentation`), `I = AffineHomImage.image φ` with projection
   `q` and closed inclusion `i`. `I` is smooth (published `AffineHomImage.smooth_image`), hence
   reduced; `q` is flat and surjective by the published `dominantGroupHomFlat`, quasi-compact,
   and locally of finite type.
2. `ρ` and `σ` kill the kernel of `q`, so they descend along `q` (published
   `FpqcHomDescent.hom` and `FpqcHomDescent.fac`) to `π₁`, `π₂` with `π₁.restrict q = ρ` and
   `π₂.restrict q = σ`.
3. `q` is surjective on rational points (`exists_rationalPoint_lift`), so restriction along `q`
   does not change images of rational-point representations. The rational-point representation
   of `i` has the image of that of `φ`, which is semisimple by
   `sum_rationalRepresentation_isSemisimple`. Since `i` is a closed subgroup,
   `identityComponent_isConnectedReductive_of_faithful h22` (module `AlgClosedCore`) proves that
   `identityComponent I` is connected reductive.
4. By `rationalRepresentation_isSemisimple_of_identityComponent` (module `AlgClosedCore`),
   `(π₁.tensor π₂).rationalRepresentation` is semisimple. Restricting along `q`
   (published `tensor_restrict`) gives `ρ.tensor σ`, with the same image.

## Provenance

Internal and derived. The route is Milne's proof of Corollary 22.44 (J. S. Milne, *Algebraic
Groups* (2017), registered as `milne-2017-algebraic-groups`, printed p. 478, PDF p. 494), with
the image of `G` in `GL_{V ⊕ W}` realized by the published `AffineHomImage` construction, and
Theorem 22.42 (printed p. 477) as the hypothesis `h22`. Milne concludes that the image is
(possibly nonconnected) reductive; here that step is the combination of the two results of
`AlgClosedCore`.
