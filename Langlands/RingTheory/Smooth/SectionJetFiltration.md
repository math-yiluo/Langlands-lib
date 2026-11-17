# Augmentation filtration of section jets

Let `ε : A →ₐ[R] R` be an augmentation of commutative algebras over a
commutative ring `R`, and put `I = ker ε`. The algebra and base ring may live
in different universes.

`Algebra.SectionJet.Quotient ε n` is the actual quotient algebra
`A/I^(n+1)`. `truncate ε n` is the natural surjective algebra map from
order `n+1` to order `n`, induced by the identity on `A`.
`Layer ε n` is its kernel, viewed as an `R`-submodule of the higher jet.
The representative criterion `mk_mem_layer_iff` says that the class of `a`
lies in this kernel exactly when `a ∈ I^(n+1)`. Thus this kernel realizes
`I^(n+1)/I^(n+2)` inside `A/I^(n+2)`.

Evaluation at the section gives `augmentation ε n`, compatible with
truncation and split by the scalar algebra map. The induced algebra
isomorphism `zeroEquiv ε` identifies the order-zero jet with `R`.

If `A` is formally smooth and of finite type over `R`, each jet is a finite
projective `R`-module by the published section-jet theorem. Projectivity of
the lower jet gives a chosen linear section `linearSection ε n` of
truncation. The map `layerProjection ε n` sends `x` to
`x - linearSection ε n (truncate ε n x)`. It is a retraction onto the
actual kernel. Consequently each `Layer ε n` is finite projective, and
`splitEquiv ε n` is an `R`-linear isomorphism from the higher jet to the
product of the lower jet and the successive layer. These sections and
splittings are choices of module maps; multiplicativity and naturality
of the choices are not claimed.

Without any smoothness or finiteness hypothesis, `cotangentEquivLayer ε`
canonically identifies `I.Cotangent` with `Layer ε 0`. Its forward map is
Mathlib's injective map `I/I² → A/I²`, with codomain restricted to the
truncation kernel. Surjectivity follows by taking a representative of a
kernel element and applying the representative criterion.
`firstLayerProjection ε` subtracts the scalar part given by the
augmentation. It yields the canonical `R`-linear isomorphism
`firstSplitEquiv ε : A/I² ≃ₗ[R] R × I.Cotangent`; its inverse sends
`(r,c)` to the scalar image of `r` plus the image of `c` in `A/I²`.
For a formally smooth finite type algebra the cotangent is therefore
finite projective, by transport across `cotangentEquivLayer ε`.

This is internal supporting algebra for the jet determinant comparison.
It is derived from the actual ideal quotient maps,
`Algebra.FormallySmooth.finite_projective_quotient_ker_pow`, and Mathlib's
projective-module lifting and ideal-cotangent APIs. The module needs no
noetherian hypothesis. It asserts neither an identification of higher
layers with symmetric powers nor a determinant or ampleness comparison.
