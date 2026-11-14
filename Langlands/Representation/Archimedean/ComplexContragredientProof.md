# Proof of `ComplexContragredientStatement`

Module: `Langlands.Representation.Archimedean.ComplexContragredientProof` (namespace
`Langlands.Archimedean.ComplexContragredient`).

Main theorem: `Langlands.Archimedean.ComplexContragredient.complexContragredientStatement :
Langlands.Archimedean.ComplexContragredientStatement.{uV}`.

## What is proved

`ComplexContragredientStatement` is stated in
`Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction`. Let `(ρ, π)` be an
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module on `V`, in the sense of the Library predicates
`IsComplexGKModule`, `IsIrreducibleGKModule` and `IsAdmissibleGKModule`. The statement asks for
an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ', π')` on a space `W` (in the same
universe as `V`) and a bilinear pairing `P : W × V → ℂ` with four properties:

- `P(ρ'(k) w, ρ(k) v) = P(w, v)`;
- `P(π'(Y) w, v) + P(w, π(Y) v) = 0`;
- `P` separates the points of `V`;
- every `U(n)`-finite linear functional on `W` (for `ρ'.dual`) is `P(·, v)` for some `v ∈ V`.

The proof takes for `W` the `U(n)`-finite contragredient: `W = kDual ρ`, the `U(n)`-finite
linear functionals on `V`, with

- `ρ'(k) w = w ∘ ρ(k)⁻¹` (`kDualRep ρ`, the restriction of Mathlib's `Representation.dual`);
- `π'(Y) w = -(w ∘ π(Y))` (`dualLie hgk`);
- `P(w, v) = w(v)`, the inclusion `(kDual ρ).subtype` read as a bilinear map.

## Proof route

The generic compact-group facts come from `Langlands.Representation.KFiniteDual`, which is
a separate helper module (candidate `2503b99f-3b40-46c3-92d6-ddab0655fbf1`). For `K = U(n)` (compact by the Library instance in
`Langlands.Global.ArchimedeanCompact`) and the clauses `hgk.1` (every vector finite) and
`hgk.2.1` (continuous coefficients) of `IsComplexGKModule`, that module gives:

- semisimplicity of `ρ` over the group algebra (`isSemisimpleModule`);
- finite-dimensional blocks under admissibility (`finiteDimensional_block`);
- clauses 1 and 2 of `IsComplexGKModule` for `kDualRep ρ` (`isFiniteVector_kDualRep`,
  `continuous_kDualRep`);
- admissibility of `kDualRep ρ` (`admissible_kDual`);
- separation of points (`exists_isFiniteVector_apply_ne_zero`);
- double duality (`exists_eq_eval`).

This module adds the Lie algebra action and the remaining clauses.

**Algebra** (section `Algebra`).

- `inv_conj_conj`: `k⁻¹ (k X k*) (k⁻¹)* = X`, using `k* k = 1`.
- `rho_inv_pi`: `ρ(k)⁻¹ π(1 ⊗ k X k*) = π(1 ⊗ X) ρ(k)⁻¹`. This is clause 4 of
  `IsComplexGKModule` for `k⁻¹`, combined with `inv_conj_conj`.
- `star_eq_neg_of_hasDerivAt`: if a curve `γ` in `U(n)` with `γ 0 = 1` has entrywise
  derivative `X` at `0`, then `X* = -X`. Differentiate the constant entries of `γ(t)* γ(t) = 1`
  with the product rule.
- `hasDerivAt_dual`: for such `γ`, `t ↦ (w ∘ ρ(γ t)⁻¹)(p)` has derivative `-w(π(1 ⊗ X) p)`
  at `0`. The inverse curve `γ(t)⁻¹ = γ(t)*` has entrywise derivative `X* = -X`. Apply clause 3
  of `IsComplexGKModule` to it with the functional `w`, and use linearity of `π` in `X`.

**The Lie algebra action** (section `DualAction`).

- `dual_dualMap_one_tmul` (from `rho_inv_pi`):
  `ρ'(k)(w ∘ π(1 ⊗ X)) = (ρ'(k) w) ∘ π(1 ⊗ k X k*)`.
- `isFiniteVector_dualMap_one_tmul`: if `w` is `U(n)`-finite, so is `w ∘ π(1 ⊗ X)`.
  - Fix a `ℂ`-basis `(e_b)` of the finite-dimensional space `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` and let `O` be the
    finite-dimensional orbit span of `w`.
  - Every `u ∘ π(1 ⊗ Z)` with `u ∈ O` lies in the range of the linear map
    `Ψ : O^B → Dual V`, `(u_b) ↦ ∑_b u_b ∘ π(e_b)`. To see this, expand `1 ⊗ Z` in the basis.
  - By `dual_dualMap_one_tmul`, every translate of `w ∘ π(1 ⊗ X)` has this form. So its orbit
    span lies in the finite-dimensional range of `Ψ`.
- `dualMap_mem_kDual`: `w ∘ π(Y)` is finite for every `Y`. The proof is induction on the
  tensor `Y` (`TensorProduct.inductionOn`), using `c ⊗ X = c • (1 ⊗ X)` and additivity.
- `dualEnd`, `dualLinear`, `dualLie`: `π'(Y) = -(π(Y))ᵀ` restricted to `kDual ρ`. It is
  `ℂ`-linear in `Y`. It is a Lie algebra homomorphism because
  `-(w ∘ π[x, y]) = -(w ∘ (π x π y - π y π x))`, which equals `[π' x, π' y] w` (a direct
  computation; the bracket on `Module.End` is the commutator).
- `hasDerivAt_kDual` (clause 3 for `(ρ', π')`). Let `S` be the orbit span of `w` together with
  `π'(1 ⊗ X) w`, a finite-dimensional subspace. Evaluations at vectors of `V` separate the
  points of `S`, so by `exists_sum_of_separating_family` the functional `ℓ` agrees on `S` with
  some `∑ aᵢ ev_{pᵢ}`. The curve `t ↦ ℓ(ρ'(γ t) w)` is then `∑ aᵢ (w ∘ ρ(γ t)⁻¹)(pᵢ)`, and its
  derivative at `0` is `∑ aᵢ (-w(π(1 ⊗ X) pᵢ)) = ℓ(π'(1 ⊗ X) w)` by `hasDerivAt_dual`.
- `kDualRep_dualLie` (clause 4): `ρ'(k) π'(1 ⊗ X) w = π'(1 ⊗ k X k*) ρ'(k) w`. Evaluate at `v`
  and use `rho_inv_pi`.
- `isComplexGKModule_kDual`: the four clauses.

**Irreducibility** (`isIrreducible_kDual`).

- Nontriviality: `V` is nontrivial, and `exists_isFiniteVector_apply_ne_zero` gives a nonzero
  element of `kDual ρ`.
- Let `W₀ ⊆ kDual ρ` be invariant under `ρ'` and `π'`. Its common kernel `A ⊆ V` is invariant
  under `ρ` and `π`, so by irreducibility of `V`, `A = ⊥` or `A = ⊤`.
  - If `A = ⊤`, every element of `W₀` vanishes on `V`, so `W₀ = ⊥`.
  - If `A = ⊥`, the image of `W₀` in the dual is a subrepresentation of `ρ.dual` that consists
    of finite vectors and separates the points of `V`. By `mem_of_separating` it contains every
    finite vector, so `W₀ = ⊤`.

**The main theorem** (`complexContragredientStatement`). Take `W = kDual ρ`, `ρ' = kDualRep ρ`,
`π' = dualLie hgk` and `P = (kDual ρ).subtype`. The `(𝔤, K)`-module, irreducibility and
admissibility clauses are `isComplexGKModule_kDual`, `isIrreducible_kDual` and
`admissible_kDual`. The four pairing properties follow:

- invariance: `w(ρ(k)⁻¹ ρ(k) v) = w(v)`;
- the Lie relation: `-w(π(Y) v) + w(π(Y) v) = 0`;
- separation: `exists_isFiniteVector_apply_ne_zero`;
- representability of finite functionals on `W`: `exists_eq_eval`.

## Provenance

This is a proof, so its route need not follow the literature. The construction is the standard
`K`-finite contragredient of an admissible `(𝔤, K)`-module; see Knapp–Vogan, *Cohomological
Induction and Unitary Representations* (1995), Chapter II, remark after (2.42). The proofs of
admissibility, irreducibility and double duality are the direct block-by-block arguments
described above and in `KFiniteDual.md`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
