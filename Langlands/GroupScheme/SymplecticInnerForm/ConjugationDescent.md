# Descending matrix algebra maps from symplectic values

Let `φ` and `ψ` be `R`-algebra homomorphisms from the matrix algebra on
`l ⊕ l` over a commutative ring `R` to the corresponding matrix algebra
over a commutative `R`-algebra `B`. Suppose that for every symplectic matrix
`g` over `R` there is a matrix `y` over `R` such that `φ y = ψ g`.

`image_of_symplectic` proves the same assertion for every matrix `X`.
The inverse image under `ψ` of the linear range of `φ` is an `R`-submodule.
The hypothesis puts all symplectic matrices in this submodule, and
`span_symplectic` therefore makes it the whole matrix algebra.

If `φ` is injective, `descendMatrixAlgHom` constructs the resulting
`R`-algebra endomorphism of the source matrix algebra.
`map_descendMatrixAlgHom` states `φ (descendMatrixAlgHom φ ψ hSp hφ X) = ψ X`.
The construction reuses the published injective algebra-map descender from
`SpecialLinearInnerForm/ConjugationDescent`: the preceding full-image result
supplies its preimages on special-linear matrices. Its algebra laws follow
by injectivity of `φ`.

This is a derived internal interface for symplectic descent, including
characteristic two and empty `l`. It assumes no choice of local conjugating
matrix and proves no existence or classification of inner forms.
