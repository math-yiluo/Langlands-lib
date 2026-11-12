# The split symplectic group scheme in matrix coordinates

This internal derived construction defines `SymplecticMatrix.groupScheme l R` for a
finite index type `l : Type` and a commutative base ring `R`. It is the split
symplectic group `Sp_{2|l|}` over `Spec R`, presented by the explicit coordinate ring

`R[X_(i,j) : i, j ∈ l ⊕ l] / (entries of X J Xᵀ - J)`,

where `J = [[0, -1], [1, 0]]` is Mathlib's `Matrix.J l`. Its points with values in a
commutative `R`-algebra `S` are exactly the matrices of Mathlib's
`Matrix.symplecticGroup l S`, that is `g ∈ M_{l ⊕ l}(S)` with `g J gᵀ = J`.

There are no inverse variables. A symplectic matrix is invertible, with inverse
`-J gᵀ J`, so Mathlib's group structure on `Matrix.symplecticGroup l S` supplies the
inverse. `SymplecticMatrix.homEquiv` identifies algebra maps out of the coordinate
ring with symplectic matrices over the target: the inverse maps specialize the
universal matrix `universal l R` and classify a matrix by its entries, and
polynomial and quotient extensionality prove that they are inverses. The
identification commutes with algebra maps (`point_comp`, `classify_map`), where
`SymplecticMatrix.map` applies a ring homomorphism entrywise.

The construction then uses the published `Corepresented.groupScheme` to put the
group-scheme structure on the relative spectrum of that ring, through the functor
`SymplecticMatrix.functor l R` of symplectic matrices and its corepresentation
`corepresentableBy l R`. The structure morphism is affine. `pointsEquiv l R T` is
the natural group equivalence, for every relative test scheme `T`, between scheme
points and symplectic matrices over `Γ(T, O_T)`; restriction along a morphism of
test schemes applies the pullback entrywise (`pointsEquiv_naturality`).

`SymplecticMatrix.inclusion` is the morphism into the published general linear
group scheme of `l ⊕ l`, induced by the natural inclusion `toGL` of symplectic
matrices into invertible matrices. `baseChangeModelIso` identifies the base change
of the model along any morphism `Spec R' ⟶ Spec R` with the model over `R'`; on
every test scheme it preserves all matrix entries
(`pointsEquiv_baseChangeModelIso_hom`).

The provenance is elementary quotient algebra, Mathlib's symplectic matrix group
(`Mathlib/LinearAlgebra/SymplecticGroup.lean`) and the published corepresented
group construction; the pattern follows the Library's `SpecialLinear.groupScheme`.
The model works over every commutative ring so that base change and smoothness
can be proved in coordinates. It is the split form used to show that the
quaternionic symplectic groups `σ.symplecticGroup H` are connected reductive. This
module proves no smoothness, connectedness or reductivity statement, and it does
not compare the model with other symplectic group schemes of the Library.
