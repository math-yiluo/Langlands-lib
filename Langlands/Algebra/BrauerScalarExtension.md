# Scalar extension on actual Brauer groups

For fields `K` and `L` in `Type u`, for any universe `u`, and any
`Algebra K L`, `Langlands.Brauer.scalarExtension L` is an additive
homomorphism from Mathlib's actual `BrauerGroup.{u,u} K` to
`BrauerGroup.{u,u} L`. There are no separability, perfection, characteristic
or local-field hypotheses. The representative algebras are actual
finite-dimensional central simple algebras.

`scalarExtension_classOf` computes the map on representatives:

`scalarExtension L (classOf A) = classOf (baseChange L A)`.

The right side is the class of the actual scalar extension `L ⊗[K] A`.
`equivalent_baseChange` proves that the map respects Mathlib's
matrix-stable equivalence. It uses `baseChangeMatrixEquiv`: the algebra
equivalence

`L ⊗[K] Matrix (Fin n) (Fin n) A ≃ₐ[L] Matrix (Fin n) (Fin n) (L ⊗[K] A)`.

This is built by writing the first factor as one-by-one matrices,
applying the Kronecker tensor equivalence and reindexing the matrix.
The scalar extension of any stabilizing equivalence is therefore another
stabilizing equivalence of the same positive sizes.

`baseChangeTensorEquiv` is the actual algebra identification

`(L ⊗[K] A) ⊗[L] (L ⊗[K] B) ≃ₐ[L] L ⊗[K] (A ⊗[K] B)`.

Its pure-tensor formula `baseChangeTensorEquiv_tmul` sends
`(l ⊗ a) ⊗ (m ⊗ b)` to `(l*m) ⊗ (a ⊗ b)`. The construction shuffles
four factors and uses `L ⊗[L] L ≃ₐ[L] L`. Together with the right unit
`L ⊗[K] K ≃ₐ[L] L`, this proves preservation of addition and zero.

`scalarExtension_self` identifies extension by `K` with the identity
homomorphism, using the actual left unit `K ⊗[K] A ≃ₐ[K] A`.
For every field tower `K → L → M` with `IsScalarTower K L M`,
`baseChangeTowerEquiv` is the actual algebra equivalence

`M ⊗[L] (L ⊗[K] A) ≃ₐ[M] M ⊗[K] A`.

Its pure-tensor formula sends `m ⊗ (l ⊗ a)` to `(l • m) ⊗ a`.
The proof reassociates the tensor factors and applies the right unit
`M ⊗[L] L ≃ₐ[M] M`. Thus `scalarExtension_tower` proves that extending
first to `L` and then to `M` equals direct extension to `M`.

The original source is Knus–Merkurjev–Rost–Tignol, *The Book of Involutions*
(1998), §1, printed pp.3–4 / PDF pp.26–27, registered as
`knus-merkurjev-rost-tignol-1998-book-of-involutions`, content SHA256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
Page 3 defines scalar extension and states its central-simple closure.
Page 4 defines matrix-stable equivalence and the tensor Brauer group.
These original pages and the retained relevant author errata were read;
no correction to these constructions was present.

The homomorphism and functoriality are derived constructions from those
definitions, implemented with the explicit algebra identifications above.
They do not assume a comparison with cohomology or a splitting theorem.
