# Projective dimension under polynomial induction

Let `R : Type u` be a commutative ring. Modules have an independent universe
`v`. The definition `polynomialModuleFunctor` sends an `R` module `M` to
`PolynomialModule R M`, regarded as an `R[X]` module, and sends an `R` linear
map to its coefficientwise extension. The supporting definition
`polynomialModuleMap` supplies the polynomial linearity of this map.
The functor is additive and preserves short exact sequences.

Under `Small.{v} R`, it also preserves projective objects.
`polynomialModule_hasProjectiveDimensionLE` proves that induction preserves
every specified finite bound on projective dimension. For an `R[X]` action
on `M` compatible with its `R` action, the theorem
`polynomialAction_hasProjectiveDimensionLE` then proves

```
pd_R(M) ≤ n  ⇒  pd_R[X](M) ≤ n + 1.
```

Here the bounds are Mathlib's categorical `HasProjectiveDimensionLE` on the
actual module objects. There is no finite-generation hypothesis. The
smallness assumption is used to compare module-theoretic and categorical
projectivity and to obtain projective presentations in `ModuleCat.{v} R`.

## Implemented proof

Functoriality and additivity follow coefficientwise. Injectivity and
surjectivity of the induced maps follow from the corresponding properties
of the coefficient maps. To prove exactness, a polynomial in the kernel
has every coefficient in the kernel; choose a preimage for each coefficient
and sum the resulting monomials over the original finite support. The zero
composite is checked on coefficients. These facts assemble into preservation
of a short exact complex.

Mathlib identifies the induced polynomial module with `R[X] ⊗[R] M`.
Its projectivity follows from the tensor-product projectivity instance
when `M` is projective. For a dimension bound, induction on `n` uses a
projective surjection onto `M`, its kernel short exact sequence, and the
short exact sequence after polynomial induction. Mathlib's dimension shift
reduces both successor bounds to the bound on the kernel. The zero case
uses preservation of projectives.

Finally, `polynomialActionShortComplex_shortExact` from
`Langlands.CommutativeAlgebra.PolynomialModuleResolution` supplies the
canonical exact sequence with two copies of the induced polynomial module
and third term `M` with its specified polynomial action. The dimension
bound on those two copies and the short exact sequence bound on the third
term give the asserted increase by at most one.

## Provenance and scope

This is an internal construction and derivation from Mathlib's polynomial
modules, tensor-product projectivity, projective presentations and dimension
shift, together with the imported polynomial-action exact sequence. It does
not translate an external literature assertion. It assumes a finite bound
for the underlying `R` module; finite presentation over `R[X]` alone does
not supply that hypothesis. Polynomial coherence, regular coherence over
valuation rings, and the geometric two-axis extension theorem remain
separate obligations.
