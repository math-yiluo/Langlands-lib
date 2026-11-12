# Finite source cosets in the original Hecke tensor

`HeckeAlgebra.rightCosetIndicator μG K hK g` is the actual compactly supported
locally constant test `1_(K*g)` on the original Hecke carrier. It is built by
right translation of the existing subgroup indicator and transported through
`HeckeAlgebra.toTestFunction`, so its carrier has the existing Hecke instances.
There is no normalization by a Haar mass.

`Homomorphism.tensor_finite_coset_normal_form` proves that every element of the
original `NonUnitalModuleTensor.Tensor (HeckeAlgebra μH) (HeckeAlgebra μG) V`
can be written

```text
Σ i : Fin n, Σ q ∈ s(i), 1_(K*q.out) ⊗ w(i,q)
```

for a single compact open subgroup `K` of `G`, finitely many finite sets
`s(i)` in `Induction.LeftQuotient K`, and actual coefficient vectors `w(i,q)`.
The right subgroup action is the published `Homomorphism.rightModule` attached
to a continuous homomorphism `φ : H →* G`; the coefficient action is the
published integrated Hecke action of a smooth representation `ρ` of `H`.
Both groups are locally compact Hausdorff nonarchimedean groups with arbitrary
supplied left Haar measures. The group universes `uG`, `uH` and coefficient
universe `v` are independent.

Only the finite sets `s(i)` are finite. The full quotient `K \ G`, the double
quotient by `H`, and the groups may all be infinite. The proof does not require
second countability, unimodularity, closedness of the homomorphism image, or
topology on the coefficient space.

The module proves the following supporting facts.

- `rightCosetIndicator_apply` identifies its value at `x` with the subgroup
  indicator at `x*g⁻¹`. `rightCosetIndicator_quotient` is the corresponding
  Kronecker identity for the quotient representative `q.out`.
- `leftInvariant_eq_quotient_out` recovers a left-`K`-invariant test's value
  from the chosen representative of its coset.
  `exists_finset_leftCoset_support` covers the test's compact support by
  finitely many open cosets `K*g`. Passing to the quotient supplies a
  finite set of cosets containing every nonzero value.
- `finite_leftCoset_expansion` combines these facts to expand the actual test
  as `Σ q ∈ s, T(q.out) • 1_(K*q.out)`. Evaluation at each point checks the
  equality, with at most one nonzero Kronecker term.
- `Homomorphism.rightModule_smul_test` proves linearity in the subgroup test
  directly from the genuine weighted right-convolution integral.
  `Homomorphism.tensor_scalar_balanced` then proves
  `(c • T) ⊗ w = T ⊗ (c • w)` in the original integer quotient.
  Choose a right local unit `a` fixing `T`, apply the original Hecke
  balancing law to `c • a`, and then to `a`. Linearity of the coefficient
  action identifies `(c • a) • w` with `a • (c • w)`.
- For the normal form, lift the tensor through the original integer-tensor
  projection and use Mathlib's finite pure-tensor representation. Choose a
  common compact open bi-invariance subgroup for all first factors.
  Expand each first factor over its finite coset support and slide its
  scalar coefficients to the second factor by the preceding theorem.

This is derived infrastructure for the fixed-vector injectivity argument in
Renard III.2.6, printed pp.76–77 / PDF pp.82–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The proofs use the existing compact support, subgroup invariance,
nondegeneracy and integer-tensor APIs. Comparison injectivity itself remains
a separate obligation.
