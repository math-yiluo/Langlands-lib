# Multilinear expansion of twisted characters of external tensor products

Let `H i` be a finite family of second-countable, locally compact, totally
disconnected Hausdorff groups. Each carries a left-invariant measure `μ i`
that is σ-finite and finite on compact sets. The product group carries
`Measure.pi μ`.

- `distribution_ext_piTensor` says that two distributions on `∀ i, H i`
  agree once they agree on every pure tensor `SchwartzBruhat.piTensor f`.
  The proof uses `SchwartzBruhat.span_piTensor`: pure tensors span the
  whole Schwartz–Bruhat space, so the difference of the two distributions
  vanishes on a spanning set.
- `twistedDistribution_external_eq_sum` handles admissible
  representations `ρ i` with operators `A i` whose factor twisted
  distributions are finite combinations
  `∑ s, c i s • twistedDistribution (μ i) (σ i s) _ (B i s)`. The twisted
  distribution of the external tensor product `FiniteTensor.external ρ`
  with the operator `PiTensorProduct.map A` is then the expanded sum over
  all choices `t : ∀ i, S i`. The coefficient of the external product of
  the chosen terms is `∏ i, c i (t i)`. On pure tensors both sides are
  products of factor values: this is the product formula
  `twistedDistribution_external_piTensor`. `Finset.prod_univ_sum` expands
  the product of sums, and `distribution_ext_piTensor` concludes.
- `twistedDistribution_external_mem_span` is the span form. Suppose each
  factor twisted distribution lies in the span of the twisted
  distributions of admissible pairs `(σ, B)` satisfying a predicate
  `Q i`. Then the external twisted distribution lies in the span of the
  twisted distributions of external tensor products of such pairs. The
  proof chooses finite expansions with `Submodule.mem_span_set'` and
  applies the expanded identity.

This is the multiplicativity of twisted characters of external tensor
products, written as an identity of distributions on the product group.
It is used for standard Levi subgroups `M = ∏ GL_{n_i}`.
