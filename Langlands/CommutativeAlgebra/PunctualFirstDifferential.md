# The first differential of a punctual perfect complex

Author: Worker 413. Worker 1015 contributed the first-differential interface
and the ideal-generation strategy.

This internal development supplies the first-differential reduction for the
punctual perfect complex proof. It is derived directly from linear algebra,
Mathlib's Nakayama lemma and the ascending chain condition, and the published
scalar-extension and homotopy constructions in
`Langlands.Cohomology.PerfectModuleComplexHomotopy`. It introduces no external
source assertion.

`exists_firstOrder_ideal_of_lt_maximal` shows that a proper subideal `I` of
the maximal ideal lies in an ideal `J` with `m² ≤ J ⋖ m`. Nakayama shows that
`I + m²` is still proper in `m`; the ascending chain condition on ideals then
supplies a maximal intermediate ideal. `ideal_eq_maximal_of_firstOrder_test`
is its contrapositive, also when the maximal ideal is zero.

`vectorOrderIdeal` is the range of evaluation of linear functionals at a
vector. Functionals send `J M` into `J`. For a free module, the converse follows
by expanding the vector in a basis with finite support, since all its
coordinates are values of linear functionals. No finite-generation assumption
on the free module is needed. These two implications are packaged in
`vectorOrderIdeal_le_iff`.

Let `L` be a cochain complex of `R`-modules, and let `e₀ : L.X 0 ≃ₗ[R] R`.
`firstDifferentialOrderIdeal L e₀` is the order ideal of
`v = (L.d 0 1).hom (e₀.symm 1)`. The lemma `firstDifferential_apply` expresses
every value of this differential as a scalar multiple of `v`. If `L.X 1` is
free, inclusion of the order ideal in `J` therefore puts the whole image of
the differential in `J • ⊤`.

`quotient_baseChange_d_eq_zero` proves that a differential with image in
`J • ⊤` becomes zero under ordinary scalar extension to `R/J`. The proof
checks the map on tensors `1 ⊗ x`, expands membership in the ideal multiple,
and moves each scalar from `J` to the quotient factor, where it is zero.
This lemma works in any degrees and requires neither freeness nor flatness.

Assume now that `L` is strictly supported in nonnegative degrees and that
`L.X 1` is free. If its first-differential order ideal lies in `J`,
`quotientHomologyZeroIsoOfFirstDifferential` constructs an actual isomorphism
`H⁰(L ⊗ R/J) ≅ R/J` in `ModuleCat (R/J)`. The incoming differential is zero
because `L.X (-1)` is zero, and the outgoing one is zero by the preceding
lemma. The standard homology and cycles isomorphisms then identify `H⁰`
with the degree-zero term. Tensoring `e₀` and using the tensor-product unit
isomorphism identifies that term with `R/J`.

`firstOrder_nonfree_of_homotopyEquiv` transfers the first-order nonfreeness
condition from a complex `K` to a homotopy-equivalent complex `L`. It applies
the published `baseChangeHomotopyEquiv` and the resulting homology isomorphism
for each quotient ring. This transfer needs only a commutative local ring.

Finally, `firstDifferentialOrderIdeal_eq_maximal` works over any commutative
Noetherian local ring. It assumes the nonnegative support, the chosen
degree-zero equivalence, freeness of `L.X 1`, maximal-ideal-valued first
differential, and the condition that `H⁰(L ⊗ R/J)` is not isomorphic to `R/J`
for every `m² ≤ J ⋖ m`. Minimality puts the order ideal in `m`. If it were
proper, the ideal-theoretic separation lemma would put it in a first-order
ideal `J`, and the constructed homology isomorphism would contradict that
condition. Thus the order ideal equals `m`, including when `R` is a field.

This supporting unit proves generation of the maximal ideal by the first
differential. It does not prove acyclicity or the final homology
identification in `RegularLocalPunctualComplexStatement`.
