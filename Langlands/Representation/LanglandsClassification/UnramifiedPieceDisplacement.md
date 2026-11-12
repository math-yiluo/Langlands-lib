# Nonzero displacement of an actual unramified geometric-lemma piece

This internal supporting unit derives a nonzero source-cone displacement for
the original unramified parameter of every nonidentity geometric-lemma piece
of two parabolics with the same actual Levi embedding. It combines the
imported normalizer correction and original-character comparison with the
proved full-parameter Weyl displacement. It transcribes no new assertion from
the literature.

Fix the supplied parabolic `p : P → G`, Levi `l : M → P`, split component
`a : A → M`, and compatible `pres : ParabolicRootPresentation p l a`.
The initial subgroup theorem works over a field and assumes the ambient group
is affine. For any `q : Q → G` and original point `z`, assume its actual
`P(k) \ G(k) / Q(k)` double coset differs from the identity double coset.
For supplied correction points `mS,mT` in `M(k)` and a normalizer point `n`,
assume the actual equation

```
n.val = (l ≫ p)(mS) * z * ((l ≫ p)(mT))^(-1).
```

`inverse_normalizerClass_not_mem_standardLeviWeyl` proves that the inverse of
the class of `n` lies outside the actual standard Levi Weyl subgroup of
`pres`. A subgroup contains a class exactly when it contains its inverse.
The existing representative theorem puts a normalizer representative of a
class in the Levi Weyl subgroup inside the actual standard Levi. Compatibility
identifies this subgroup with the point image of the specified `l ≫ p`.
Multiplication and inversion in that image, applied to the correction equation,
then put `z` in the same Levi image and hence in the source parabolic. The
explicit double-coset relation would make the original double coset the
identity, a contradiction. No comparison with a Weyl double-coset space is
needed.

The real-parameter section additionally uses a nonarchimedean local field and
assumes the ambient group is locally of finite type. Let `D` be an arbitrary
supplied `GeometricLemmaIntersectionDatum` for `p` and `q`, whose target Levi
map `lQ : M → Q` satisfies `lQ ≫ q = l ≫ p`. Assume `G` is connected reductive
and supply `R : RelativeRootReflectionData pres.data.i`. For an original
unramified Levi character `ψ`, assume its existing component parameter belongs
to `restrictedCorootChamber pres.data.i pres.data.ν pres.data.J pres.data.f R`.
These are the supplied chamber and reflection data, not an existence assertion
for such data or characters.

For every supplied component factor `b : A → D.L'` with
`b ≫ D.lQ' ≫ D.q' = a`, the theorem
`D.normalizedRealPart_piece_eq_sub_nonzeroCone_of_nonidentity` gives a vector
`δ ∈ pres.nonnegCone`, `δ ≠ 0`, with

```
normalizedRealPart (ψ ∘ (b ≫ D.φ.hom ≫ D.l' ≫ D.p'))
  = leviUnramifiedRealPart ψ - δ.
```

The source is still the original character pulled through the original piece
maps. The proof constructs the two Levi corrections by the imported common-torus
argument. The subgroup theorem excludes the inverse normalizer class from the
Levi Weyl subgroup. The imported full-parameter displacement theorem gives
`δ`, and the imported normalized-real-part comparison identifies its inverse
Weyl translate with exactly this original pullback.

`D.unramifiedPieceRealPart_eq_sub_nonzeroCone_of_nonidentity` specializes the
formula to `b = groupHom f ≫ a'` for any supplied `a' : A' → D.L'` and
`f : A → A'` whose composite with `D.lQ' ≫ D.q'` is `a`. Its left side is
exactly the existing `D.unramifiedPieceRealPart pres.isCompatible.splitComponent
a' f ψ`. No split-component property of `a'` is needed for this character
comparison; it will be needed separately for tempered exponent transfer.

The definition `D.unramifiedPieceDisplacement pres ψ a' f` is the existing
Levi component parameter minus this existing piece parameter.
`D.unramifiedPieceDisplacement_mem_nonnegCone_and_ne_zero` proves that the
actual difference lies in `pres.nonnegCone` and is nonzero under the same
hypotheses. The sign is the source parabolic cone sign. This unit does not yet
identify the opposite parabolic cone, establish spectral separation of the
full tempered twisted piece, or prove the host regularity proposition.
