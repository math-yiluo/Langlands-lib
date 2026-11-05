# Minimal polynomial relations between primitive elements

This internal algebraic result works over an arbitrary field `k : Type u`,
with a commutative bialgebra `B : Type w` over `k`. The coefficient field,
bialgebra and variable index type have independent universes. No
characteristic, perfectness, infinitude or smoothness hypothesis is imposed.

`exists_additive_relation` states that if a finite family of primitive
bialgebra elements `x : Fin n → B` has a nonzero polynomial relation, it
has a nonzero relation `f` satisfying `TorusLinearization.IsAddPoly`.
That predicate asserts additivity on tuples in every commutative
`k`-algebra in the coefficient universe, not only on field-valued points.
The conclusion retains `aeval x f = 0`. It does not assert that every
polynomial relation is additive.

The supporting construction `additiveComul` on `P = MvPolynomial J k`
sends each variable to `X j ⊗ 1 + 1 ⊗ X j`. The linear map
`reducedComul` sends `f` to

`additiveComul f - f ⊗ 1 - 1 ⊗ f + f₀ (1 ⊗ 1)`,

where `f₀` is its constant coefficient. `lowerTensorSpan D` is the linear
span of pure tensors whose two polynomial factors each have total degree
strictly less than `D`. `reducedComul_mem` proves that the reduced
coproduct of `f` belongs to `lowerTensorSpan f.totalDegree`.

For this bound, the proof first treats monic monomials. It identifies their
exponents with multisets of variables and inducts by adjoining one
variable. For a polynomial `g` with zero constant coefficient, the product
formula is

`reducedComul (g X j) = reducedComul g * additiveComul (X j)
  + g ⊗ X j + X j ⊗ g`.

Multiplication by `additiveComul (X j)` raises the degree of at most one
factor by one. The constant and single-variable cases have zero reduced
coproduct. Finally, linearity and the coefficient-support expansion prove
the bound for an arbitrary polynomial, including cancellation among terms.

`eq_zero_of_tensor_map_eq_zero` provides the linear algebra step. If a
linear map `E : P →ₗ[k] V` is injective on polynomials of degree at most
`D - 1`, then its tensor square detects zero on `lowerTensorSpan D`.
An algebraic linear left inverse on that degree subspace extends to `V`.
The tensor square of this retraction fixes every generating pure tensor,
and hence the entire span. No finite dimension of `V` is assumed.

Evaluation at primitive bialgebra elements respects the coproduct.
Applying the counit to a relation gives zero constant coefficient, and
the tensor square of evaluation kills its reduced coproduct. The proof
of `exists_primitive_relation` chooses a nonzero relation of minimum total
degree. That degree is positive. Evaluation is injective on all smaller
degrees, so the preceding retraction shows that its reduced coproduct is
zero. Its constant coefficient is zero as well, giving
`additiveComul f = f ⊗ 1 + 1 ⊗ f`. This supporting result permits an
arbitrary index type `J`.

For `J = Fin n`, applying the tensor-product algebra map defined by two
arbitrary tuples turns this coproduct identity into universal additivity.
This proves the advertised nonzero additive relation. The proof uses a
minimum total degree and the tensor retraction, without a multivariate
Taylor expansion. Its provenance is the internal argument described here;
it is a separate finite-variable extension of the relation principle
already used for two elements in `Unipotent.OneDimensional.Relation`.

This unit supplies the polynomial-relation step for later coordinate
arguments. It does not itself supply primitive algebra generators,
prove independence of a specified family, or construct a vector-group
isomorphism or a split series.
