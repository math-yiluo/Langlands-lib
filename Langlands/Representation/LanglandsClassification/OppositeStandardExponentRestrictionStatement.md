# Restriction of opposite standard exponents to a larger standard Levi

Worker 5295, Task 5295. This module defines the closed proposition
`OppositeStandardExponentRestrictionStatement`. It is an input of the
reduction of the exponent-selection step in Renard VII.4.2 (iii) (the
published internal `OppositeJacquetUntwistSelectionStatement`). Nothing is
proved here.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026. The main locator is VII.4.2, proof of
Theorem (iii), printed p.244 / PDF p.250. The statement combines Lemma VII.1.1
(normalized exponents, printed p.220 / PDF p.226) with the transitivity of
parabolic restriction. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The statement

The universes are `u`, of the field, and `v`, of the representation carrier;
they are independent. The proposition quantifies over the following data:

- a nonarchimedean local field `k` (`Field`, `ValuativeRel`, topology,
  `IsNonarchimedeanLocalField`, `T2Space`);
- a connected reductive group scheme `G` over `k`, whose rational points carry
  the canonical point topology and are locally compact and a nonarchimedean
  group;
- a torus monomorphism `i : T → G` that is a maximal split torus;
- a generic cocharacter `ν` whose dynamic parabolic is a minimal parabolic.
  It determines the positive and simple relative roots `Δ` and the standard
  labels `J ⊆ Δ` (`StandardJacquetFamily.Index i ν`);
- integral root-reflection data `D`, which supplies the coroots `α̌`;
- an admissible smooth representation `π` of `G(k)` of finite length, on a
  carrier in universe `v`.

The published family `OppositeStandardJacquetFamily.exponents i ν hG hi hν π`
consists of the pairs `x = (J, χ)`. Here `J` is a standard label and `χ` is an
actual normalized Jacquet exponent of `π` (VII.1.1). It is taken along the
actual opposite `P̄_J` of the standard parabolic `P_J`, as a character of the
chosen split component `A_J` of the standard Levi `M_J`. Its full real
parameter `v_x = OppositeStandardJacquetFamily.fullRealPart … D x` lies in
`Vstar T = ℝ ⊗ X*(T)`. It is the unique vector that annihilates the coroots of
`J` and restricts on `A_J` to the normalized real part of `χ` (published in
`OppositeStandardExponentParameters`).

**Assertion.** Fix an exponent `z` with label `J`, a standard label `K` with
`J ⊆ K`, and a vector `w ∈ Vstar T`. Assume:

1. `⟨w, α̌⟩ = 0` for every relative root `α ∈ K`;
2. `v_z − w` lies in the real span of the vectors `1 ⊗ α`, `α ∈ K`.

Then there is an exponent `x` with label exactly `K` and `v_x = w`.

## Correspondence with the source

In the proof of (iii), printed p.244, Renard takes the Langlands decomposition
`μ = μ⁺ + μ⁻ + μ_G` of a real exponent `μ` of `r^G_{P̄}(π)` (with `Q = LU` the
standard parabolic of the decomposition). He writes: since `μ⁻|_{A_L}` is
trivial, Lemma VII.1.1 and the transitivity of the parabolic restriction
functors give

`μ|_{A_L} = μ⁺ + μ_G ∈ ℜ(Exp(A_L, r^G_{Q̄}(V)))`.

In the ambient realization used here, `L` is the standard Levi of `K` and `w`
plays the role of `μ⁺ + μ_G`:

- The roots of `K` restrict trivially to `A_K`. So hypothesis 2 implies that
  `w` and `v_z` have the same restriction to `A_K`, which is the restriction
  `μ|_{A_L}` of the source. (The converse also holds, because the kernel of
  this restriction is exactly the span of `K`, but it is not needed.)
- Hypothesis 1 says that `w` lies in the coroot annihilator of `K`. Restriction
  to `A_K` is injective on that annihilator, so `w` is the full parameter of
  this restriction.

The conclusion is the source's membership of `μ|_{A_L}` in the real parts of
the exponents of `r^G_{Q̄}(π)`, read in full parameters: some exponent on the
label `K` has full real parameter `w`. The statement concerns only full real
parameters. It does not identify the restricted character itself, and it does
not assert uniqueness.

Provenance: derived. This is an intermediate claim of the source proof,
isolated as a closed proposition. The expected proof combines:

- the normalized transitivity `r^G_{P̄_J} ≅ r^{M_K}_{P̄_J ∩ M_K} ∘ r^G_{P̄_K}`
  of the actual Jacquet functors;
- Lemma VII.1.1 (ii): the exponents of a Jacquet module of an admissible
  representation of `M_K` restrict on the central `A_K` to exponents of that
  representation;
- functoriality of normalized real parts along the inclusion of `A_K` into
  `A_J`.

None of these steps is carried out here.

The hypotheses `π.IsAdmissible` and `π.HasFiniteLength` are those under which
Renard's exponents are defined and finite. They match the hypotheses of the
published finiteness and selection lemmas for the same family.
