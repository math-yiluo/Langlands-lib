# Coefficient averaging on a single source coset

`normalizedSourceCosetTest H μG μH K hK x` is the actual Hecke test

```text
μH(H ∩ x K x⁻¹)⁻¹ • 1_(K*x⁻¹).
```

The coefficient subgroup is exactly the published
`Induction.conjOpenSubgroup H K x`. Let `G` be a locally compact Hausdorff
nonarchimedean group, `H` a closed subgroup, `μG` and `μH` arbitrary
supplied left Haar measures, and `ρ` a smooth complex representation of `H`
on the algebraic vector space `V`. The definition of the test itself needs
no closedness assumption; closedness is used in its supporting identities to
make the coefficient subgroup compact and its Haar mass finite and positive.

The central identity `tensor_sourceCoset_value` says that the original tensor
`1_(K*x⁻¹) ⊗ w` equals this normalized source test tensored with its elementary
comparison value at `x`. This is an equality in the original
`NonUnitalModuleTensor.Tensor`, with the original Hecke actions.

The proof follows these steps.

- `compact_cosetCoefficientSubgroup` expresses the actual coefficient subgroup
  as the inverse image of `K` under the closed embedding
  `h ↦ x⁻¹ h x`. `haarScale_conjugate` proves invariance of the ambient
  modular factor under conjugation. Hence
  `haarScale_cosetCoefficient` and
  `relativeModularCharacter_cosetCoefficient` prove that the ambient and
  relative modular factors are one on the coefficient subgroup.
- `compactSubgroupTest_sourceCoset` identifies the comparison subgroup test
  at `x` with its unnormalized coefficient-subgroup indicator.
  `rightRepresentation_sourceCoset_fixed` checks that this subgroup fixes
  `1_(K*x⁻¹)` under the genuine right distribution representation.
- `tensor_sourceCoset_average` uses the normalized coefficient-subgroup
  indicator, its invariance under distribution inversion, and the original
  Hecke balancing relation. It replaces `w` by its integrated compact
  average without changing the original tensor.
- `compactComparisonValue_sourceCoset` identifies the elementary comparison
  value with that same average multiplied by the Haar mass.
  `tensor_sourceCoset_value` cancels this nonzero mass and moves its inverse
  to the first factor using the proved scalar-balancing identity.

The module also proves compatibility with changing representatives.
For `h : H` and `k : K`, `sourceCoset_representative_test` identifies the test
at `h*y*k` with `haarScale(h)` times the right distribution translate of the
test at `y`. The formula for that representation supplies the reciprocal
modular factor, which cancels in evaluating the indicator.
`tensor_sourceCoset_representative` then uses the original tensor's scalar
and group balancing to give

```text
1_(K*(h*y*k)⁻¹) ⊗ w
  = 1_(K*y⁻¹) ⊗ (haarScale(h) • ρ(h⁻¹)w).
```

This is derived infrastructure for the compact-open fixed-vector argument in
Renard III.2.6, printed pp.76–77 / PDF pp.82–83, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original compact comparison, coset test, and tensor balancing modules
supply its inputs. It does not itself assert injectivity of the comparison.

The group and coefficient universes `uG` and `v` are independent. There is
no finiteness of the double-coset space, second countability, unimodularity,
or coefficient topology assumption.
