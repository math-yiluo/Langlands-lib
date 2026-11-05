# Affine tensor coordinates and canonical coefficient conjugation

This internal coordinate construction starts with an actual affine presentation
`Spec A ≅ X` over `Spec k`. The standard tensor-spectrum pullback comparison
gives `Spec (K ⊗[k] A) ≅ X_K`, with the tensor factors ordered as in
`TensorGaloisPoint`. Its first projection is induced by `a ↦ 1 ⊗ a`, followed
by the chosen presentation of `X`; its field projection is induced by
`c ↦ c ⊗ 1`. Passing to global sections gives `sectionsEquiv`.

The canonical semilinear scheme map fixes the projection to `X` and composes
the projection to `Spec K` with `Spec σ`. The pullback universal property
identifies this map, in the tensor coordinates, with the spectrum of
coefficient conjugation. Neither this comparison nor the coordinate
construction requires a finite or Galois extension.
