# Compact induction from an open normal subgroup: fixed vectors and coinvariants

This module proves two general facts about the compact induction
`compactInduced H σ` (Langlands/Representation/Induction/Definitions) from an
open normal subgroup `H` of a topological group `G`. Both are internal helper
results, not stated in the literature. They were written for the Lean proof
`inducedProgeneratorCenterInclusion` of the centre inclusion `ℨ_Ω ⊂ ℨ_D`
(Renard 2026, VI.10.4, second Lemma, printed p. 211, PDF p. 217), applied to
the progenerator `Π_D = c-Ind_{⁰M}^{M}(ρ₀)`. Renard proves that Lemma with the
free `ℨ_D`-module structure of `R_Ω` (the first Lemma of VI.10.4) and the
generic irreducibility VI.8.5, so these facts are not taken from his proof. In
the Lean proof, the first fact proves that `Π_D` has the no-fixed-vector
property that `CuspidalSupport/SelfIntersectionPieceVanishing` requires. The
second is used to show that `Π_D` is supercuspidal
(`CuspidalSupport/RationalSummandInductionSupercuspidal`).

## `compactInduced_eq_zero_of_fixed`

**Statement.** Let `H` be an open normal subgroup of `G`, `σ` a representation
of `H`, and `t ∈ G` an element such that `tⁿ ∉ H` for every `n > 0`. If a
compactly induced function `f` satisfies `compactInduced H σ t f = f`, then
`f = 0`.

**Proof.**
1. By induction on `n`, `f` is fixed by `tⁿ` for every `n : ℕ`. So by
   `eval_compactInduced`, the underlying function satisfies
   `f(x tⁿ) = f(x)` for all `x`.
2. Suppose `f ≠ 0`. Then there is a point `x` with `f(x) ≠ 0`, by
   `compactFunctions_ext`.
3. The map `n ↦ H x tⁿ` into `H \ G` is injective. If `H x tᵐ = H x tⁿ`,
   then `x tⁿ t⁻ᵐ x⁻¹ ∈ H`. Since `H` is normal, `tⁿ t⁻ᵐ ∈ H`, so
   `t^{|n-m|} ∈ H`, and the hypothesis forces `m = n`.
4. Every coset `H x tⁿ` lies in the support quotient
   `quotientSupport H f` because `f(x tⁿ) = f(x) ≠ 0`. This set is finite by
   `quotientSupport_finite`, which uses that `H` is open. An infinite family of
   distinct points in a finite set is a contradiction
   (`Set.infinite_of_injective_forall_mem`).

## `compactInduced_restrict_mem_relations`

**Statement.** Let `H` be an open normal subgroup of `G` and `π` a
representation of `G` whose restriction `π|_H` is smooth. Let `U ≤ H` be a
subgroup such that every vector of `π` lies in the `U`-coinvariant relations
`Jacquet.Localization.relations π U 1`, the span of the vectors
`π(u) w - w`. Then every function `f` in `compactInduced H (π|_H)` lies in the
`U`-coinvariant relations of that compact induction.

In other words, if the `U`-coinvariants of `π` vanish, then so do the
`U`-coinvariants of `c-Ind_H^G(π|_H)`.

**Proof.**
1. `cosetSum_unitMap` (Induction/OpenAdjunction) writes `f` as the finite sum,
   over cosets `H x`, of the terms `cosetTerm … f (H x)`. Since the relations
   form a submodule, `finsum_induction` reduces the claim to one term.
2. Fix a representative `x` of the coset. Define the linear map
   `Ψ = cI(x⁻¹) ∘ unitMap ∘ π(x) : V → c-Ind_H^G(π|_H)`, where `unitMap` is
   the unit of the open-subgroup adjunction.
3. `Ψ` intertwines `U`: `Ψ(π(u) w) = cI(u) Ψ(w)` for `u ∈ U`. This holds because
   `x u x⁻¹ ∈ H` (normality, `U ≤ H`), `π(x) π(u) = π(x u x⁻¹) π(x)`, and
   `unitMap` is `H`-equivariant.
4. So `Ψ` maps each generator `π(u) w - w` of the relations of `π` to the
   generator `cI(u) Ψ(w) - Ψ(w)` of the relations of the compact induction
   (`sub_mem_relations`). Hence it maps the relations of `π` into those of the
   compact induction.
5. By `cosetTerm_quotientMap`, the term at `H x` equals `Ψ(π(x⁻¹) f(x))`. By
   hypothesis `π(x⁻¹) f(x)` lies in the relations of `π`, so the term lies in
   the relations of the compact induction.
