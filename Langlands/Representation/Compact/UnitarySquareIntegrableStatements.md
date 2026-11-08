# Unitary and square-integrable representations: statements

Author: Worker 6. Module `Langlands.Representation.Compact.UnitarySquareIntegrableStatements`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.2.2, Corollary (i) (printed p.98 / PDF p.104), and IV.3.2–IV.3.3 (printed pp.99–102 / PDF pp.105–108). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

- **IV.2.2, Corollary (i).** If `G` has a countable basis of neighbourhoods of the identity and `(π, V)` is unitary and admissible, then `dim End_G(V) = 1` if and only if `π` is irreducible.
- **IV.3.2, Definition.** For `G` unimodular with Haar measure `dg*` on `G/Z(G)`, a smooth `(π, V)` is square-integrable modulo the centre if `Z(G)` acts by a unitary character `χ` and every matrix coefficient `φ_{v,λ}` lies in `L²(G, χ, dg*)`. It is essentially square-integrable if `π ⊗ ω` is square-integrable modulo the centre for some character `ω` of `G`.
- **IV.3.2, Proposition.** An irreducible smooth representation that is essentially square-integrable modulo the centre is admissible.
- **IV.3.2, Lemma.** An admissible smooth representation that is square-integrable modulo the centre is unitary and semisimple.
- **IV.3.3, Lemma.** (i) For `π` irreducible and essentially square-integrable modulo the centre, there is a real `d(π) > 0`, the formal degree, with `∫_{G/Z(G)} φ_{v₁,λ₁}(g) φ̌_{v₂,λ₂}(g) dg* = λ₁(v₂) λ₂(v₁) / d(π)`, where `φ̌(g) = φ(g⁻¹)`. (ii) For two non-equivalent such representations with the same central character, the same integral vanishes.
- **IV.3.3, Corollary.** For pairwise non-equivalent irreducible essentially square-integrable `π₁, …, π_r` with the same central character and nonzero `vᵢ`, `λᵢ`, the coefficients `φ_{vᵢ,λᵢ}` are linearly independent. The same holds for irreducible compact representations.

## The Lean statements

The module is a statement unit: nothing is proved. Throughout, `G : Type u` is a t.d. group: `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]`. Smooth representations are the published `SmoothRep.{0, u, v} ℂ G`. In the IV.3 statements, `G ⧸ Subgroup.center G` carries a Borel structure and a Haar measure `μ` that is also right invariant, which is how the published `IsSquareIntegrableModCenter` statements express Renard's unimodular `dg*`. Renard's `Ṽ` is the published `SmoothDual`, the smooth vectors of the algebraic dual.

1. `UnitaryAdmissibleEndomorphismStatement` (IV.2.2 Cor (i)): with `[FirstCountableTopology G]`, for `π` with `π.IsAdmissible` and `IsUnitarizable π.representation`, `Module.finrank ℂ (π.representation.IntertwiningMap π.representation) = 1 ↔ π.IsIrreducible`. `Module.finrank` is `0` on infinite-dimensional spaces, so the left side says the endomorphism space is exactly one-dimensional.
2. `EssentiallySquareIntegrableAdmissibleStatement` (IV.3.2 Prop): for irreducible `π`, a character `ω : G →* ℂˣ` with open kernel (a smooth character) and the twist `π.twist ω hω` (the published `SmoothRep.twist`), if there is a `UnitaryCentralCharacter` `c` of the twist with `MemLp (c.coefficientNorm ℓ x) 2 μ` for every smooth functional `ℓ` and vector `x`, then `π.IsAdmissible`. This is "essentially square-integrable" with admissibility not assumed. The published `IsSquareIntegrableModCenter` builds admissibility into its definition, so it cannot be used here.
3. `SquareIntegrableUnitarySemisimpleStatement` (IV.3.2 Lemma): `IsSquareIntegrableModCenter π.representation μ → IsUnitarizable π.representation ∧ Representation.IsSemisimpleRepresentation π.representation`. No irreducibility is assumed. The published `SquareIntegrableUnimodularUnitarityStatement` is the irreducible case of the unitarity part, under its own second-countability and cofinality hypotheses.
4. `SchurOrthogonalityStatement` (IV.3.3 Lemma). Write `EssSqInt π` for "some smooth twist of `π` has a unitary central character and square-integrable smooth coefficients", as in 2.
   - (i) For irreducible `π` with `EssSqInt π`, there is `d : ℝ` with `0 < d` such that for all `x₁ x₂ : π`, `ℓ₁ ℓ₂ : SmoothDual π.representation` and every `F : G ⧸ Z(G) → ℂ` with `F (mk g) = ℓ₁(π(g) x₁) · ℓ₂(π(g⁻¹) x₂)`, both `Integrable F μ` and `∫ q, F q ∂μ = ℓ₁(x₂) · ℓ₂(x₁) / d`.
   - (ii) For irreducible `π₁`, `π₂` with `EssSqInt`, not isomorphic (`IsEmpty (π₁ ≅ π₂)`), and acting on the centre by the same character `χ : Z(G) →* ℂˣ`, every such `F` (built from `π₁`, `π₂`) is integrable and has integral `0`.

   The integrand descends to `G / Z(G)` because the central characters cancel. The statement quantifies over the descended function `F`, characterized by its values, instead of constructing it. Integrability is part of each conclusion, not a hypothesis. This records the convergence of the source's integrals; the Bochner integral alone would be `0` for a nonintegrable function. The formulas then assert their values.
5. `CoefficientLinearIndependenceStatement` (IV.3.3 Corollary): for `π : Fin r → SmoothRep`, all irreducible and `EssSqInt`, pairwise non-isomorphic, with a common central character, and nonzero `x i`, nonzero `ℓ i : SmoothDual (π i).representation`, the family `i ↦ matrixCoefficient (π i).representation (ℓ i) (x i)` of functions `G → ℂ` is linearly independent over `ℂ`.

`UnitarySquareIntegrableStatements` is the conjunction of the five statements.

## Remarks

- The Corollary's last sentence (irreducible compact representations) is not stated; the companion IV.1.3 Lemma statement (candidate `a59f332c-60db-44f2-9991-a34ed1e0de20`) gives compactness of the centre in that case.
- The IV.3.2 Remark (one nonzero square-integrable coefficient suffices for irreducible `π`), the space `L²(G, χ, dg*)₀` of IV.3.1 (published as `MatrixCoefficient.CentralL2`), and the IV.2.2 Proposition and Corollary (ii) (published as `AdmissibleUnitarySemisimplicityStatement`) are not restated here.
- The proofs are not formalized here.
