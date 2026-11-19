# Polynomial product decomposition after Galois splitting

Let `A` be a module-finite algebra over `R = k[X₁, …, Xₙ]`. Suppose that
after extension to `S = E[X₁, …, Xₙ]`, for a Galois extension `E/k`, it
becomes a finite power of `S` as an `S`-algebra. The theorem
`mvPolynomial_product_of_galois_split` gives a ring equivalence from `A`
to a finite product of polynomial rings over fields. The index type and
the fields have the same universe as `k` and `A`.

The pushout for polynomial rings identifies the base change with
`E ⊗[k] A`. A basis of `A` over `k` expresses each tensor by a finite
family of coefficients in `E`. A tensor fixed by all `k`-automorphisms
of `E` has its coefficients in `k`, so it lies in the image of
`a ↦ 1 ⊗ a`.

A polynomial over a finite product of rings corresponds to a tuple of
polynomials over the factors. For the inverse, the finite union of the
supports contains the support of the coefficient tuple. In a polynomial
ring over a field each idempotent is zero or one. It follows that in the
split algebra idempotents are constant polynomial tuples. The conjugated
Galois action fixes the variables and maps diagonal constants to diagonal
constants. The coordinate idempotents and diagonal constants generate
all coefficient tuples. It follows that coefficient extraction commutes
with the action.

The proof defines `B` as the `k`-subalgebra of `A` whose image in the split
polynomial ring is constant. Each coefficient of the image of an element
of `A` descends to `B`, by the fixed tensor calculation. Evaluating
polynomials with coefficients in `B` at the original variables gives an
isomorphism with `A`. Its composite with the embedding in the split
polynomial ring is the injective change of coefficients induced by the
embedding of `B` in the product of fields. For surjectivity, each
coefficient of an image polynomial lifts to `B`.

Evaluation at zero through that isomorphism gives a surjective map from
`A` to `B` that is semilinear over the origin evaluation `R → k`.
Module finiteness of `A` over `R` gives module finiteness of `B` over `k`.
The coefficient embedding makes `B` reduced, so it is an Artinian
reduced ring. Mathlib identifies it with the product of its residue
fields at its finitely many maximal ideals. Applying the finite-product
polynomial equivalence gives the stated result. The constructions allow
zero variables and an empty product.

This is an algebraic proof of the descent needed in the geometric route
to `AffineSpaceFiniteEtalePolynomialProductStatement`. The splitting
itself is a hypothesis. The implementation uses Mathlib's pushout,
infinite Galois fixed-field, and Artinian ring decomposition theorems.
