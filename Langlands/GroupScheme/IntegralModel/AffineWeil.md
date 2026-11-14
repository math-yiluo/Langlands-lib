# Integral models formed by actual affine Weil restriction

This derived constructor packages an actual affine Weil restriction as an
integral model with an explicitly supplied generic identification. It also
identifies the original special-fibre map of every compatible extension.

Let `A` be a domain with fraction field `F`, and let `B` be a finite
projective commutative `A`-algebra. Let `X, Y` be smooth affine group schemes
over `B`, and `G, H` group schemes over `F`. All types lie in an arbitrary
common universe `u`.

Given
`e : AffineWeil.BaseChange.source A B F X ≅ G`,
`IntegralModel.affineWeil A F B X e` has the actual restricted group
`AffineWeil.groupScheme A B X` as its integral group and `e` as its generic
identification. Here `BaseChange.source` is the base change to `F` of the
original restriction. Affineness and finite type follow from the affine
restriction construction; its smoothness theorem supplies flatness.
`affineWeil_isSmooth` records smoothness of the resulting model.

Suppose also
`d : AffineWeil.BaseChange.source A B F Y ≅ H`,
`f : X ⟶ Y`, and `g : G ⟶ H`. The hypothesis

```text
BaseChange.sourceMap A B F X f ≫ d.hom = e.hom ≫ g
```

is the actual generic compatibility square. Under that hypothesis,
`affineWeilHom` constructs a model homomorphism over `g` whose underlying
map is `AffineWeil.map A B f`. `affineWeil_hom_eq` applies generic rigidity
to prove that every homomorphism between these two models over the same
`g` has exactly this underlying map.

If `A` is also local, `affineWeil_specialFibreMap_eq` identifies every
such extension's `specialFibreMap` with
`AffineWeil.BaseChange.sourceMap A B (IsLocalRing.ResidueField A) X f`.
After the rigidity rewrite, the equality is definitional: the model's
residue base map is the same `Spec` map used by the restriction's field
base change.

This is internal assembly from `AffineWeilSmooth`, `AffineWeilBaseChange`
and the integral-model generic rigidity theorem. The generic isomorphisms
and compatibility square remain inputs. The constructor does not prove a
generic identification for a particular root group or identify arbitrary
supplied root models.
