# Injectivity from prescribed elementary comparison values

`finiteCosetReconstruction` is an additive map from the original relatively
twisted compact induction into the original Hecke tensor quotient. For a
compact open `K` and a finite set `s` of double cosets in `H \ G / K`, it is

```text
f ↦ Σ q ∈ s, normalizedSourceCosetTest(q.out) ⊗ f(q.out).
```

The test in each term is the actual test `1_(K*q.out⁻¹)` divided by the
subgroup Haar mass of `H ∩ q.out K q.out⁻¹`. No support assertion is needed
to define this finite additive map.

The final theorem `compactComparison_injective_of_pure_values` proves
injectivity of any additive map `F` from the original tensor into the original
compact induction whose elementary-tensor values equal the prescribed
`compactComparisonFunction`. The group is an arbitrary locally compact
Hausdorff nonarchimedean group `G`, `H` is a closed subgroup, and both Haar
measures are arbitrary supplied left Haar measures. The coefficient
representation is smooth and complex-linear on an algebraic vector space `V`.
The group and carrier universes `uG` and `v` are independent.

The premise of this theorem is the equality of the complete elementary
comparison functions for every test `T` and coefficient `w`. It does not
assume injectivity, a reconstruction identity, a global inverse, or any
condition on quotient cardinalities.

`comparisonTensor` and `comparisonTensorTmul` are reducible abbreviations
making the exact original right action and integrated coefficient action
explicit. Their bodies are the existing `NonUnitalModuleTensor.Tensor` and
`NonUnitalModuleTensor.tmul`; no different group, tensor relation, or scalar
structure is introduced.

The implemented proof has the following steps.

1. `finiteCosetReconstruction_apply` identifies the additive map with the
   displayed finite sum. Each summand is the original tensor's biadditive
   map composed with evaluation of actual compact functions.
2. `compactComparisonValue_sourceCoset_zero` proves that the comparison of
   `1_(K*x⁻¹) ⊗ w` vanishes at every point in a different double coset.
   Otherwise a nonzero subgroup-test value would give
   `g = h*x*k`, contradicting the double-coset distinction.
3. `tensor_sourceCoset_chosen_value` uses a double-coset decomposition
   `x = h*q.out*k`. The proved representative-change tensor identity rewrites
   the tensor at the chosen representative, and the proved single-coset
   averaging identity recovers it from its comparison value there.
   Applying `F` to the same tensor identity makes this the actual value of
   `F` at `q.out`.
4. `finiteCosetReconstruction_sourceCoset` sums over any finite set containing
   that double coset. All other terms vanish by step 2, and step 3 identifies
   the remaining term with the original source-coset tensor.
5. For an arbitrary tensor, `tensor_finite_coset_normal_form` supplies one
   compact open subgroup and finitely many coset-indicator tensors.
   The finite union of their double cosets defines a reconstruction that
   recovers every term, and hence the given tensor, by additivity. If its
   image under `F` is zero, additive reconstruction of that zero is zero;
   therefore the original tensor is zero.

This proof is derived from the compact-open fixed-vector argument of Renard
III.2.6, printed pp.76–77 / PDF pp.82–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
It uses the proved finite-coset, averaging, scalar-balancing and group-balancing
identities on the original carriers. There is no finite-index, compact-quotient,
second-countability, unimodularity, or topology-on-coefficients hypothesis.
Construction of the balanced comparison map, its naturality, and the final
categorical isomorphism are supplied by separate modules.
