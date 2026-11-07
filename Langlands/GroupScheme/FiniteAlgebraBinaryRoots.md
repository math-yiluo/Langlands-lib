# Actual binary elementary maps over finite algebras

Let `k : Type u` be a field and `D : Type u` a `k`-algebra with only a
`Ring D` assumption. Choose bases `bD : Basis (Fin d) k D` and
`bA : Basis (Fin n) k (Matrix (Fin 2) (Fin 2) D)`. No commutativity,
division, central simplicity, separability, or characteristic assumption on
`D` is used.

The namespace `Langlands.GroupScheme.FiniteAlgebraUnits.BinaryRoot`
constructs actual group-scheme homomorphisms `upperMap` and `lowerMap` from
the vector group of dimension `d` over `k` into the previously constructed
unit group scheme of the binary matrix algebra. For every relative test
scheme `T`, the vector coordinates determine the tensor parameter

`a = ∑ i, x_i ⊗ bD i ∈ Γ(T, O_T) ⊗[k] D`.

Under `MatrixPoints.tensorMatrixEquiv`, the two actual morphisms send this
point to the invertible matrices `[1,a;0,1]` and `[1,0;a,1]`, respectively,
with the explicit inverses from `Langlands.BinaryElementary`. The
theorems `tensorMatrixEquiv_upperMap` and `tensorMatrixEquiv_lowerMap`
state these formulas on every test, and `upperPoints_naturality` and
`lowerPoints_naturality` prove compatibility with every actual test
pullback.

The scalar-extended basis proves `parameterHom_surjective` and
`tensorCoordinates_surjective`. Consequently, `exists_upperPoint` and
`exists_lowerPoint` realize every upper or lower elementary matrix over
the tensor coefficient algebra as the image of an actual additive test
point. This includes nonreduced coefficient algebras and arbitrary
relative test schemes.

This is an internal construction from the existing actual matrix point
models, vector-group coordinates, and elementary matrix identities.
The proof first packages the additive elementary formulas as monoid
homomorphisms and proves that arbitrary ring maps preserve them. Tensor
coefficient naturality and the natural vector coordinates then give
natural point homomorphisms. `homOfPoints` constructs the actual
group-scheme morphisms, and its evaluation formula proves the displayed
matrix identities. Surjectivity follows from the sum-of-coordinates
identity for the base-changed basis.

This unit concerns the full matrix-algebra unit scheme. It does not
assert reduced-norm-one membership, construct the diagonal cocharacter
or its contractions, prove arithmetic generation or SK1, or prove the
general local Kneser–Tits proposition.
