# Local unit generators for a unit cocycle along a faithfully flat algebra

Author: Worker 1072.

This module states one proposition, `Langlands.Algebra.UnitCocycleLocalUnitsStatement`
(universe parameter `u`). It is the affine algebraic input to the effectivity of
faithfully flat descent of unit cocycles to line bundles
(`Langlands.Scheme.Modules.UnitCocycleDescentEffectiveStatement`). It is only stated
here, not proved or assumed.

## Statement

```text
∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
  (u v : S ⊗[R] S), u * v = 1 →
  map (AlgHom.id R S) includeRight u = includeRight u * map (AlgHom.id R S) includeLeft u →
  Ideal.span {r : R | ∃ m m' : S, u * (m ⊗ₜ 1) = 1 ⊗ₜ m ∧
    v * (m' ⊗ₜ 1) = 1 ⊗ₜ m' ∧ algebraMap R S r = m * m'} = ⊤
```

Here `map` is `Algebra.TensorProduct.map`, and `includeLeft`, `includeRight` are
Mathlib's `Algebra.TensorProduct.includeLeft` and `includeRight`, all over `R`.
In words: let `R → S` be a faithfully flat homomorphism of commutative rings and let
`u` be a unit of `S ⊗_R S` with inverse `v`. Write, for `s ⊗ t ∈ S ⊗_R S`,

- `u₁₂` for the image of `u` under `s ⊗ t ↦ s ⊗ (t ⊗ 1)`
  (Lean: `map (AlgHom.id R S) includeLeft u`),
- `u₂₃` for the image of `u` under `s ⊗ t ↦ 1 ⊗ (s ⊗ t)` (Lean: `includeRight u`),
- `u₁₃` for the image of `u` under `s ⊗ t ↦ s ⊗ (1 ⊗ t)`
  (Lean: `map (AlgHom.id R S) includeRight u`),

all in `S ⊗_R (S ⊗_R S)`. Suppose the cocycle identity `u₁₃ = u₂₃ · u₁₂` holds.
Put

```text
M_u = {m ∈ S | u · (m ⊗ 1) = 1 ⊗ m},   M_v = {m' ∈ S | v · (m' ⊗ 1) = 1 ⊗ m'}.
```

Then the elements `r ∈ R` whose image in `S` is a product `m · m'` with `m ∈ M_u` and
`m' ∈ M_v` generate the unit ideal of `R`. The proposition quantifies `R`, `S`, the
algebra structure, faithful flatness, `u`, `v` and both hypotheses explicitly. It assumes
no finiteness or noetherian hypothesis.

## Provenance

Provenance: derived. The proposition is not stated in this form in the literature; it is
a consequence of faithfully flat descent for modules, specialised to the rank-one
module `N = S`. The source is The Stacks Project Authors, *Descent*, version ed88ff78,
registered as `stacks-descent-ed88ff78-2026`.

- Definition 3.1 (Tag 023G), PDF p.4, with the notation on PDF p.5: a descent datum
  for modules relative to `R → A` is an `A`-module `N` with an isomorphism of
  `A ⊗_R A`-modules `φ : N ⊗_R A → A ⊗_R N` satisfying the cocycle condition
  `φ₀₂ = φ₁₂ ∘ φ₀₁`, where `φ₀₁ = φ ⊗ id_A`, `φ₁₂ = id_A ⊗ φ` and
  `φ₀₂(n ⊗ 1 ⊗ 1) = Σ aᵢ ⊗ 1 ⊗ nᵢ` when `φ(n ⊗ 1) = Σ aᵢ ⊗ nᵢ`.
- Proposition 3.9 (Tag 023N), PDF p.8: if `R → A` is faithfully flat, every descent
  datum is effective, and the descended module is
  `M = {n ∈ N | 1 ⊗ n = φ(n ⊗ 1)}`, with `A ⊗_R M → N` an isomorphism.

Take `A = S` and `N = S`. Then `N ⊗_R S` and `S ⊗_R N` are both `S ⊗_R S`, and an
`S ⊗_R S`-linear isomorphism `φ` is multiplication by a unit `u`. The three maps of
Definition 3.1 become multiplication by `u₁₂`, `u₂₃` and `u₁₃` (in the indexing
`0, 1, 2` of the source: `φ₀₁ ↔ u₁₂`, `φ₁₂ ↔ u₂₃`, `φ₀₂ ↔ u₁₃`), so the cocycle
condition is exactly `u₁₃ = u₂₃ · u₁₂`, the hypothesis above. Stacks' descended module
`{n | 1 ⊗ n = φ(n ⊗ 1)}` is exactly `M_u`. The inverse `v` gives the inverse descent
datum, with descended module `M_v`.

The conclusion is derived as follows. By Proposition 3.9, `S · M_u = S` and
`S · M_v = S`, so `S · (M_u · M_v) = S`. Each product `m · m'` with `m ∈ M_u`,
`m' ∈ M_v` satisfies `1 ⊗ mm' = mm' ⊗ 1` (multiply the two defining equations and use
`uv = 1`), hence lies in the image of `R` by faithfully flat descent of elements. So the
ideal `I` of the statement satisfies `I · S = S`, and `I = R` because `R → S` is
faithfully flat. In geometric terms: `M_u` is an invertible `R`-module, and the
conclusion says that it is free of rank one, with generator `m` and `m · M_v ⊆ R`, on a
cover of `Spec R` by basic open sets `D(r)`. This is the local freeness used to show that
the descended module is a line bundle.

The proof is not part of this module; the route above records only why the proposition
is a faithful derived consequence of the cited source.
