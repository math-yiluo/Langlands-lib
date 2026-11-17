# Reduction of the Mumford Rosati trace formula to the characteristic-zero degree statement

This module defines a reduction proposition and proves it.

## The proposition

`Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceCharZeroReductionStatement` is

`IsogenyDegreeTateDeterminantCharZeroStatement.{u} → MumfordEulerDegreeStatement.{u} → MumfordMixedEulerTraceStatement.{u}`.

The three propositions are existing published or staged Library statements:

- `Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroStatement` (S1₀): over an algebraically closed field of characteristic zero and for every prime `p`, the degree of an endomorphism of an abelian scheme is the determinant of its rational `p`-adic Tate map, and that determinant is `0` for a non-isogeny.
- `Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement` (S2): for an ample Mumford presentation `lam` of `L` and an endomorphism `f`, the map `n • lam + f ≫ lam ≫ f^∨` is an isogeny of degree `χ(f^* L ⊗ L^n)^2` for all large `n`.
- `Langlands.AbelianScheme.Rosati.MumfordMixedEulerTraceStatement`: the target of Task 7330. It assumes `[CharZero k]`.

All three are used at the same universe `u`. The theorem `Langlands.AbelianScheme.Rosati.mumfordMixedEulerTraceCharZeroReduction` proves the reduction. It uses no premise beyond S1₀ and S2.

Provenance: this is an internal reduction. It is the reduction `MumfordMixedEulerTraceReductionStatement` of the module `Langlands/AlgebraicGeometry/Picard/MumfordRosatiMixedEulerTraceReduction.lean`, with its first premise, the degree statement `IsogenyDegreeTateDeterminantStatement` for all characteristics, replaced by its characteristic-zero case S1₀. The target's field has characteristic zero, so the earlier proof only applies the degree statement in characteristic zero, at the prime `2`.

## Proof

The module imports `MumfordRosatiMixedEulerTraceReduction` and reuses all its helper results that do not mention the degree statement. Those are in the namespace `Langlands.AbelianScheme.Rosati.MumfordTraceReduction`. Their descriptions are in that module's Markdown file. The reused results include the algebra lemmas, `rational_two_finrank`, `nonempty_left`, the polarization lemmas `exists_integral_inverse` and `det_rationalMap_comp_inverse`, the rank lemma `finrank_comp_of_isIsogeny`, and the Euler-polynomial lemmas `euler_facts`, `mixed_pullback_id` and `mixed_self_eq`.

The four results of that module that take the degree statement as a hypothesis are restated here, in the namespace `Langlands.AbelianScheme.Rosati.MumfordTraceCharZeroReduction`, with the hypothesis `hS1 : IsogenyDegreeTateDeterminantCharZeroStatement.{u}`. Each proof is the earlier proof word for word, except that each application `hS1 k A 2 h2 α` of the general statement, with `h2 : ((2 : ℕ) : k) ≠ 0`, becomes the application `hS1 k A 2 α` of S1₀, and the line introducing `h2` is dropped. The field `k` has characteristic zero in all four.

- `trace_rationalMap_mem_range`: for an integral `α`, the trace of the actual `2`-adic Tate map of `α` is rational. The value of `charpoly (-V α)` at a natural number `n` is `det V(n • 𝟙 + α)`. By the two clauses of S1₀ it is a rank or `0`, so it is rational. Lagrange interpolation (`coeff_mem_range_of_eval_natCast`) makes the next coefficient, the trace, rational.
- `primeEndomorphismTrace_mem_range`: the same for every rational endomorphism, by `Rationalization.exists_integral_multiple`.
- `algebraMap_geometricEndomorphismTrace`: the Library's chosen trace `geometricEndomorphismTrace A a` maps to the actual `2`-adic trace `primeEndomorphismTrace A 2 a`, by `geometricEndomorphismTrace_eq`.
- `key_identity`: with `β = involution (homToHom0 f) * f`, twice the coefficient of degree `g - 1` of the Euler polynomial of `f^* L` equals its coefficient of degree `g` times the `2`-adic trace of `β`. For all large `n` the rank of `(n • lam + f ≫ lam ≫ f^∨) ≫ μ` is computed twice. S2 and the rank of a composite give `χ(f^* L ⊗ L^n)^2 · rank μ`, and the first clause of S1₀ gives `N ^ (2g) · det(n + V β)`. The coefficients of `n ^ (2g)` and `n ^ (2g - 1)` are then compared.

The final theorem `mumfordMixedEulerTraceCharZeroReduction` is the earlier final theorem word for word, using these four results. The case `f = 𝟙` of `key_identity` shows that the subleading pure Euler coefficient of `L` vanishes. The general case, `geometricEndomorphismTrace_mul_comm` and `algebraMap_geometricEndomorphismTrace` then give the target formula after injectivity of `algebraMap ℚ ℚ_[2]`.
