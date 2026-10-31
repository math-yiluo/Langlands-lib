# From a trivial tangent kernel to cotangent surjectivity

This internal supporting statement concerns schemes `X` and `Y` over an
arbitrary field `K`, all in an arbitrary common universe. Their structural
morphisms are `p` and `q`, and `f : X ⟶ Y` satisfies `f ≫ q = p`.
The point `x : Spec K ⟶ X` is rational in the project's sense:
`Picard.IsRationalPoint p x` means `x ≫ p = 𝟙 (Spec K)`.

Write `z = x(closedPoint K)`. Equip the actual structure-sheaf stalks at
`z` and `f(z)` with the canonical algebras `Picard.stalkAlgebraOver`.
The augmentation `r = Picard.rationalStalkAugmentation p x hx` is the
canonical map from the source stalk to `K`.
The map `a = Picard.stalkMapAlgHomOver p q f h z` is the actual
contravariant stalk map, regarded as a homomorphism of these `K`-algebras.
Its direction is `𝒪(Y,f(z)) →ₐ[K] 𝒪(X,z)`, and its underlying ring
homomorphism is `(f.stalkMap z).hom`.
The imported augmentation compatibility identifies `r.comp a` with the
canonical rational augmentation at `x ≫ f`, namely
`Picard.rationalStalkAugmentation q (x ≫ f)
  (Picard.isRationalPoint_comp_over p q f h x hx)`.

The hypothesis says that every actual tangent morphism
`t : Spec (K[ε]/(ε²)) ⟶ X` at `x` whose image under `f` is constant
is itself constant. A tangent morphism is over `K` and restricts to `x`
along the zero section, as specified by `Picard.IsTangentVectorAt`.
The constant tangent is `Picard.dualNumberProjection K ≫ x`.

The conclusion is surjectivity of `augmentationCotangentMap r a`, the
`K`-linear map

```text
ker(r ∘ a) / ker(r ∘ a)²  →  ker(r) / ker(r)².
```

Thus the conclusion refers to the actual stalk map and the canonical rational
augmentations, rather than to auxiliary rings or an assumed surjectivity
certificate. Each augmentation is onto because it splits the scalar map;
its kernel is the maximal ideal of the corresponding local stalk. This
identifies these augmentation cotangent spaces with the usual cotangent
spaces at the rational points.

The formulation is derived internally from the project's actual tangent and
stalk adapters. Cotangent functionals give augmented dual-number maps;
stalk naturality turns their precomposition into postcomposition by `f`.
The expected proof uses the tangent-kernel hypothesis and linear duality.
No external theorem is transcribed here. This file defines a proposition
and supplies no proof of it.

The characteristic is arbitrary. No algebraic-closure, finite-type,
properness, reducedness, smoothness, or finite-dimensionality hypothesis is
imposed. The statement concerns only the specified rational point and makes
no closed-immersion claim.
