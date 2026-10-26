# Bounded cyclic decomposition of an annihilated polynomial module: proof

`Langlands.polynomialModuleBoundedCyclicDecomposition.{uK, uV}` proves the
published, unchanged proposition
`Langlands.PolynomialModuleBoundedCyclicDecompositionStatement.{uK, uV}` from
`Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement`.
Its type is exactly that proposition, with the same universe parameters.

## What is proved

For every field `K : Type uK`, every finite-dimensional `K`-vector space
`V : Type uV`, every `K`-linear endomorphism `f` of `V` and every polynomial `c`
with `c ≠ 0` and `Polynomial.aeval f c = 0`, there are a natural number `m` and a
tuple `q : Fin m → Polynomial K` with `m ≤ Module.finrank K V`, each `q i` monic
and dividing `c`, and a `Polynomial K`-linear equivalence from
`Module.AEval' f` to the product over `i : Fin m` of the quotients
`Polynomial K ⧸ Ideal.span {q i}`. No hypothesis is added: the field has
arbitrary characteristic, and the zero-dimensional case is covered (there the
bound forces `m = 0`).

## The implemented proof

The module has one auxiliary definition, one auxiliary theorem and the main
theorem, all in namespace `Langlands`. Write `K[X]` for `Polynomial K` and
`M` for `Module.AEval' f`.

### Main theorem

`polynomialModuleBoundedCyclicDecomposition` introduces the binders. Mathlib's
`Module.AEval.isTorsion_of_aeval_eq_zero` turns `aeval f c = 0` and `c ≠ 0` into
`Module.IsTorsion K[X] M`, and Mathlib's instance
`Module.AEval.instFinitePolynomial` makes `M` finitely generated over `K[X]`
because `V` is finite-dimensional over `K`. Mathlib's structure theorem
`Module.equiv_directSum_of_isTorsion` for finitely generated torsion modules
over a principal ideal domain then supplies a finite index type `ι`, irreducible
`p i`, exponents `e i` and an equivalence from `M` to the direct sum of the
quotients `K[X] ⧸ (p i ^ e i)`. Composing with
`DirectSum.linearEquivFunOnFintype` presents `M` as the finite product of these
quotients. The irreducibility of the `p i` is discarded, and the auxiliary theorem
below is applied with `r i := p i ^ e i`.

### Auxiliary theorem `exists_bounded_of_equiv_pi`

In namespace `Langlands.PolynomialModuleBoundedCyclicDecomposition`, this
theorem takes the same `K`, `V`, `f` and `c` with `c ≠ 0` and `aeval f c = 0`,
an arbitrary finite index type `ι`, an arbitrary family `r : ι → K[X]`, and a
`K[X]`-linear equivalence `E` from `M` to the product of the quotients
`K[X] ⧸ Ideal.span {r i}`. It concludes the existential of the target statement.
Its proof has five steps.

1. **`c` annihilates the product.** For `x : M`, the element `c • x` is zero:
   applying the inverse of Mathlib's `K`-linear identification
   `Module.AEval.of K V f` turns `c • x` into `(aeval f c)` applied to a vector,
   which is zero by hypothesis. Transporting along `E` shows `c • y = 0` for
   every `y` in the product.
2. **Every `r i` divides `c`.** Apply step 1 to the element with the class of
   `1` in factor `i` and zero elsewhere (`Pi.single`). Its `i`-th coordinate is
   the class of `c • 1 = c`, so `c` lies in `Ideal.span {r i}`, that is,
   `r i ∣ c` (`Ideal.mem_span_singleton`). Since `c ≠ 0`, each `r i` is nonzero.
3. **Removal of trivial factors.** If `r i` is a unit, then
   `Ideal.span {r i} = ⊤` and the quotient is a subsingleton. The auxiliary
   definition `piRestrictOfSubsingleton` (below) restricts the product to the
   subtype `S` of indices with `r i` not a unit; this is a `K[X]`-linear
   equivalence. Then `m` is the cardinality of `S`, and
   `LinearEquiv.piCongrLeft'` reindexes the product along
   `Fintype.equivFin S : S ≃ Fin m`.
4. **Monic generators.** For `j : Fin m`, `q j` is `normalize` of the
   corresponding `r`. It is associated with that `r`, so the two principal
   ideals are equal (`Ideal.span_singleton_eq_span_singleton`), and
   `Submodule.quotEquivOfEq` applied coordinatewise
   (`LinearEquiv.piCongrRight`) gives the final equivalence `E'` from `M` to the
   product of the quotients `K[X] ⧸ Ideal.span {q j}`. Each `q j` is monic by
   `Polynomial.monic_normalize`, since the `r` it comes from is nonzero, and
   divides `c` by step 2 and `normalize_dvd_iff`.
5. **The bound `m ≤ finrank K V`.** Each remaining quotient is nontrivial: its
   generator `q j` is associated with a non-unit, hence is not a unit, so its
   ideal is not `⊤` (`Submodule.Quotient.nontrivial_iff`). The product is a
   finite `K`-module because `E'`, with scalars restricted to `K`, is a
   `K`-linear equivalence from the finite-dimensional `M`. The `K`-linear map
   `φ : (Fin m → K) → product`, `φ a = (j ↦ a j • 1)`, built with
   `LinearMap.pi` and `LinearMap.smulRight`, is injective: if `a j • 1 = 0` with
   `a j ≠ 0`, multiplying by `(a j)⁻¹` gives `1 = 0` in a nontrivial quotient.
   Hence
   `m = finrank K (Fin m → K) ≤ finrank K (product) = finrank K M = finrank K V`,
   using `Module.finrank_fin_fun`,
   `LinearMap.finrank_le_finrank_of_injective`, the restricted equivalence `E'`
   and `Module.AEval.of K V f`.

When every `r i` is a unit, or `ι` is empty, step 3 gives `m = 0` and the empty
product; no case split is needed.

### Auxiliary definition `piRestrictOfSubsingleton`

For a semiring `R`, a predicate `P` on an index type and a family of
`R`-modules `Q i` such that `Q i` is a subsingleton whenever `P i` fails, this
`R`-linear equivalence sends a family `x` to its restriction to the subtype
`{i // P i}`. The inverse extends by zero outside `P`. The inverse laws hold
because the omitted factors have only one element.

## Provenance

The argument follows the route proposed in the statement's Markdown and in the
task: Mathlib's PID structure theorem, removal of trivial cyclic summands,
normalization of generators, divisibility from annihilation, and one nonzero
vector per remaining summand for the bound. It is an internal algebraic
prerequisite specified by Worker 39 for task
`e82ee8d6-204c-40ac-85b0-968fb0a6a298`, not a quotation from an external
source. The proof uses no uniqueness of elementary divisors and no
characteristic-polynomial formula. It depends only on Mathlib and the statement
module, and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
