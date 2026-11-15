# The algebra `A[x, z]/(xᵢⁿ − Σⱼ zᵢⱼ aⱼ)`

This module supports the proof of Stacks Lemma 10.3 (Tag 07FE). Fix a ring `A`, natural
numbers `d` and `n`, and `a : Fin r → A`. Let

`SmoothingAlgebra.Alg d n a = A[xᵢ, zᵢⱼ]/(xᵢⁿ − Σⱼ zᵢⱼ aⱼ)`, for `i < d` and `j < r`.

In Lemma 10.3 the `aⱼ` generate the singular ideal of `A` over a field `k`. The source
writes this algebra as `B = A[x₁, …, x_d, zᵢⱼ]/(xᵢⁿ − Σ zᵢⱼ aⱼ)`.

## Structure

`Alg` is a `def` with the following data:
- `CommRing`, `Algebra A`, `Algebra k` and `IsScalarTower k A` instances;
- the quotient map `mk`;
- the identity `rel_eq : xᵢⁿ = Σⱼ zᵢⱼ aⱼ`;
- an algebra structure over `k[x₁, …, x_d]` with `xᵢ ↦ xᵢ` (`instAlgebraPoly`, with
  `algebraMap_X`).

It is finitely presented over `k` and over `k[x]` when `A` is finitely presented over `k`.

## Smoothness

`formallySmooth_away` and `smooth_away` prove: if `A_{aⱼ}` is (formally) smooth over `k`,
then `Alg_{aⱼ}` is (formally) smooth over `k[x]`. This is the source's "Each `B_{aⱼ}` is
smooth over `R`: it is a polynomial algebra over `A_{aⱼ}[x₁, …, x_d]`".

The Lean proof checks the lifting property directly. Let `J ⊆ T` be a square-zero ideal
and `φ : Alg_{aⱼ} → T/J` a `k[x]`-algebra map.

1. **Lift `A_{aⱼ}`.** Lift `A_{aⱼ} → T/J` to `α : A_{aⱼ} → T` by formal smoothness over `k`.
2. **Send the generators.**
   - Send `xᵢ` to the image of `xᵢ` in `T`.
   - Send `zᵢₗ` to a lift `tᵢₗ` of `φ(zᵢₗ)`.
   - Correct `zᵢⱼ` by `α(aⱼ)⁻¹ εᵢ`, where `εᵢ = xᵢⁿ − Σₗ tᵢₗ α(aₗ)`.
3. **The relations.** The relations then map to zero. `εᵢ` lies in `J`, so the
   corrected values still lift `φ`.
4. **Extend.** The map extends over the localization because `α(aⱼ)` is a unit.

Finite presentation follows from `IsLocalization.Away.finitePresentation` and
`Algebra.FinitePresentation.trans`.

## The map to `Λ`

Given `f : A → Λ` and `πᵢ` with `πᵢⁿ = Σⱼ λᵢⱼ f(aⱼ)`, `lift` is the `k[x]`-algebra map
`Alg → Λ` with `xᵢ ↦ πᵢ` and `zᵢⱼ ↦ λᵢⱼ`. Here `Λ` is a `k[x]`-algebra with `xᵢ ↦ πᵢ`. The
lemma `lift_algebraMap` shows that `lift` restricts to `f` on `A`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), proof of Lemma 10.3 (Tag 07FE, p. 25).
