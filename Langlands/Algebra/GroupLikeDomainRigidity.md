# Integral parameter rigidity for group-like coalgebras

This is an internal algebraic prerequisite for actions on full, possibly
nonsmooth, diagonalizable centres. Let `k` be a field, `R` an integral
commutative `k`-algebra, and `C` a `k`-coalgebra spanned by its group-like
elements. The group-like elements of `R ⊗[k] C` are exactly `1 ⊗ g`, for the
original group-like elements `g` of `C`. No reducedness of `C` is assumed.

The proof extends the existing field-extension argument in
`Langlands.Algebra.GroupLikeBaseChange`: the group-like basis extends to an
`R`-basis, while linear independence of distinct group-like elements over an
integral ring excludes any additional element.

For a rational specialization `ε : R →ₐ[k] k`, an `R`-coalgebra endomorphism
of `R ⊗[k] C` which specializes to the identity is the identity. The proof
first treats a group-like basis vector: its image is a pure extended
group-like element, and specialization identifies that element with the
original one. Basis extensionality gives equality on the whole coalgebra.

This result alone does not assert existence of a torus containing a reductive
centre, triviality of a group-scheme action, or the semigroup comparison.
