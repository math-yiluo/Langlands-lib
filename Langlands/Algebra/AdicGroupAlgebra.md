# Algebraization of compatible maps into group algebras

Worker 891.

This module constructs algebra and bialgebra homomorphisms into group algebras
from compatible maps over all adic quotients. It implements the algebraic part
of SGA 3, Exposé IX, Theorem 7.1, recomposed pp.56–58 (original margins
pp.68–72), using Lemma 7.2 through `AdicDiagonalAlgebraization`. The registered
source is `sga3-expose-ix-gille-polo-2009`, SHA-256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
The `System` interface is an internal adaptation of the source's Hopf-algebra
argument: it retains the coefficient form of the coproduct equations and works
with maps from the original algebra rather than bundling their scalar extensions.

Let `A` be a commutative ring, `I` an ideal, `C` a commutative `A`-algebra,
and `M` an arbitrary commutative additive group. These types have independent
universes. For a linear map `d : C →ₗ[A] C ⊗[A] C`, `System I d` comprises:

- algebra maps `fₙ : C →ₐ[A] AddMonoidAlgebra (A/Iⁿ) M`;
- agreement of their coefficients under the quotient maps for every `n ≤ k`;
- the diagonal coefficient equations
  `tensorCoefficient fₙ m k (d x) = if m = k then coeff(fₙ x,m) else 0`.

The coefficient maps in the last line include the finite coefficient families
in all coefficient families. Indexing includes the zero quotient `A/I⁰`.
`reduce I n` is the coefficientwise quotient algebra map on `A[M]`.

When `A` is noetherian and `I`-adically complete and separated,
`System.toCoefficientSystem` feeds this data into the companion finite-support
construction. `liftLinear` identifies the resulting finitely supported family
with an element of `A[M]`. The exact reduction equation `reduce_liftLinear`
holds at every power. Since all reductions are algebra maps, they imply that
the linear lift preserves `1` and multiplication: the proof uses
`eq_of_reduce_eq`, which checks each coefficient modulo all ideal powers.
`System.liftAlgHom` is the resulting actual algebra map, and
`liftAlgHom_unique` states its uniqueness among algebra maps with those
reductions.

The proof of `System.map_d` compares the two coproduct tensors using the
standard linear equivalence `A[M] ⊗[A] A[M] ≃ₗ[A] A[M × M]`.
`tensorEquiv_map_coeff` identifies its entries with `tensorCoefficient`,
while `comul_coeff` computes the diagonal entries of the group-algebra
coproduct. The companion limit construction passes the input equations to
the limit, proving that the algebraized map respects `d`.

If `C` is an `A`-bialgebra and `d` is its actual comultiplication, assume in
addition that, for every `n` and `x`, the counit of `fₙ(x)` over `A/Iⁿ` is the
reduction of the counit of `x` over `A`. The lemma `counit_reduce` proves
naturality of the group-algebra counit by induction on finite coefficient
families. Separatedness then proves the counit equation for `liftAlgHom`.
`liftBialgHom` bundles the result as an actual bialgebra homomorphism
`C →ₐc[A] AddMonoidAlgebra A M`. It realizes every input reduction by
`reduce_liftBialgHom` and is unique by `liftBialgHom_unique`.

No smoothness, finite presentation, flatness, or finite generation condition
on `C` or `M` is imposed. This module does not provide the adapter from
compatible group-scheme maps or from scalar-extended bialgebra maps to its
input system, and does not perform finite étale descent. Those remain
obligations toward the full group-scheme adic lifting theorem of Task 7014.
