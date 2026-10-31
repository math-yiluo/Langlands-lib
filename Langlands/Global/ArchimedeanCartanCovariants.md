# Actual compact covariants of the Cartan symmetric algebra

Author: Worker 94. This is an internal construction from the actual Cartan symmetric action, finite-span algebraic compact averaging, and the abstract finite-covariant argument in `Langlands.Algebra.ReynoldsCovariants`.

Let `K` be a number field in any universe and let `n` be any natural number, including zero. Write `S = CartanSymmetricAlgebra K n` for the actual symmetric algebra of the complexified Cartan complement, and `A = cartanSymmetricCompactInvariants K n` for its subalgebra fixed by every element of `standardInfiniteCompact K n`. For each `τ : ContinuousCompactRep K n`, the module `CartanSymmetricCovariantModule K n τ` is
`M = S ⊗[ℂ] (Fin τ.dim → ℂ)`.
The action is the actual diagonal representation: conjugation on `S` and the given continuous representation `τ` on the other factor. The scalar action of `S` on `M` multiplies the left tensor factor.

`cartanSymmetricCovariantRepresentation_tmul` gives this action on pure tensors. Tensor induction proves `cartanSymmetricCovariantRepresentation_smul`, its semilinearity with respect to conjugation of coefficients. Consequently the tensors fixed by the whole compact subgroup form the actual `A`-submodule `W = cartanSymmetricCovariants K n τ`.

Every orbit in `τ` has finite continuous span: the ambient space is finite dimensional, each algebraic linear functional on it is continuous, and the orbit maps of `τ` are continuous. The coefficient action has finite continuous orbits by `ArchimedeanCartanAveraging`. Bilinear closure for the tensor map proves the property for pure tensors in `M`; tensor induction and additive closure prove it for all of `M`. No topology on the infinite-dimensional tensor module is assumed.

The compact subgroup carries its Borel measurable structure. Internally, Haar measure is normalized on the whole group, whose compactness makes this a probability measure. `cartanSymmetricCovariantAverage` is the scalar-dual finite-span average, with codomain restricted to `W`. Left invariance gives fixedness under every compact element, and normalization gives `cartanSymmetricCovariantAverage_fixed`: the average of each vector of `W` is itself. No choice of measure appears among the parameters of the public declarations.

Two applications of equivariant naturality supply the compatibility needed for finite covariants. Multiplication by `a : A` is a complex-linear equivariant endomorphism of `M`, since conjugation fixes `a`. Thus `cartanSymmetricCovariantAverage_smul` makes the projection `A`-linear, giving `cartanSymmetricCovariantReynolds`. For any fixed tensor `x : W`, the complex-linear map `S → M` sending `P` to `P • x.val` is equivariant by semilinearity and fixedness of `x`. Naturality now gives `cartanSymmetricCovariantAverage_coefficient`:

```text
average_M (P • x.val) = average_S P • x.
```

The module and coefficient averages use the same normalized Haar measure on the same Borel group. The coefficient average in this identity is exactly `cartanSymmetricCompactAverage K n`, and its `A`-linear form is `cartanSymmetricCompactReynolds K n`.

`cartanSymmetricCovariantReynoldsPair` packages these two actual projections, the fixed-vector identity and the displayed coefficient law. The coefficient algebra `S` is Noetherian by the previously constructed finite-dimensional Cartan complement and the symmetric-algebra finiteness argument. The tensor module `M` is finite over `S`, by base change from the finite-dimensional space underlying `τ`. The abstract theorem `ReynoldsPair.moduleFinite_of_noetherianRing` therefore proves `cartanSymmetricCovariants_moduleFinite`: `W` is finite over `A`. Its argument takes finitely many fixed tensors spanning `S • W` in the Noetherian ambient module and projects their coefficient expressions back to `W`, replacing every ambient coefficient by its Reynolds average in `A`.

This result concerns symmetric algebras of vectors and their actual full-compact fixed tensors. Full-group invariant restriction finiteness, trace duality with polynomial functions, PBW, central generation, admissibility and the final differential-growth theorem remain separate obligations.
