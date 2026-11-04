# The trace coefficient `ψ_H` in Schur orthogonality (proof of Waldspurger III.7.1)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceOrthogonality`,
namespace `Langlands.HarishChandraSchwartz`. It imports `SchurOrthogonality`
(`orthogonalityIntegrand`, `orthogonalityIntegrand_mk`, `orthogonalityIntegral`,
`integrable_orthogonalityIntegrand`, `orthogonalityIntegral_eq_zero_of_integrable`,
`formalDegree`, `orthogonalityIntegral_eq_formalDegree`) and `TraceCoefficientFamily`
(`traceCoefficient`, `traceCoefficient_eq_sum`, `averageProjection`, `averageProjection_apply`,
`fixedFunctional`); from the representation-theory part of the Library it uses
`Langlands.Representation.Smooth.Contragredient.FixedVectorsProof`
(`smoothDualFixedRestriction_apply`), `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`
(`smoothDualFixedRestriction_bijective`), `isSmooth_smoothContragredient`,
`Jacquet.compressedAction_apply`, `Jacquet.smoothDualPairing_averageMap`,
`Jacquet.map_averageMap_of_forall_eq` and `Compact.averageMap_id`; from Mathlib
`LinearMap.trace_conj'`, `LinearMap.trace_transpose'`, `Module.Basis.sum_repr` and
`MeasureTheory.integral_finsetSum`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082.
Printed page numbers; the PDF page is the printed page minus 234.

- Proof of Proposition III.7.1, printed p. 274 (PDF p. 40): for `(ω, E) ∈ O` and a compact open
  subgroup `H`, `ε_H` is `(mes H)⁻¹` on `H` and `0` outside, and
  `ψ_H(g) = trace[ω̌(ε_H) ω̌(g) ω̌(ε_H)]`. For irreducible tempered `π` and `v`, `v̌` fixed by
  `H`, the computation of `⟨π[ϕ] v, v̌⟩` leads to
  `f_χ = [G : G¹A_G]⁻¹ ∫_{A_G \ G} ψ_H(g) ⟨π(g) v, v̌⟩ χ⁻¹(g) dg`.
- Same proof, printed p. 275 (PDF p. 41): "D'après III.1 (2), qui se généralise au cas où `π_2`
  est seulement tempérée, cette intégrale est nulle si `π ≄ ω ⊗ χ`. Si `π ≃ ω ⊗ χ`, elle vaut
  `d(π)⁻¹ ⟨v, v̌⟩` d'après III.1 (3)."

The module proves these two evaluations of `∫ ψ_H(g) ⟨π(g) v, v̌⟩ dg` for a representation
`ω` in place of Waldspurger's `ω ⊗ χ`; the twist by `χ⁻¹`, the Fourier inversion on
`G¹A_G \ G` and the identity `d(π) = d(ω)` are not formalized. The identity
`ψ^{ω̌}_H(g) = ψ^ω_H(g⁻¹)` and the reduction of the integral to a finite sum of Schur
orthogonality integrals are derived steps of this module; Waldspurger states the evaluations
directly.

## Scope: abstract data and explicit hypotheses

The setting is that of `SchurOrthogonality`: `G` is a topological group
(`[IsTopologicalGroup G]`), `A` is a normal subgroup (`[A.Normal]`; for the second evaluation
also `hA : A ≤ Subgroup.center G`), `G ⧸ A` carries a Borel measurable structure, and
`μ` is a Haar measure on `G ⧸ A` that is invariant under inversion. The representations
`π : Representation ℂ G V` and `ω : Representation ℂ G W` act on `A` by one character
`χ : A →* ℂˣ` (`hπ`, `hω`). `H` is a compact open subgroup (`CompactOpenSubgroup G`). Waldspurger's
`A_G`, his Haar measure and his `G¹` are not identified here. The hypotheses of each result are:

- `traceCoefficient_smoothContragredient`: `[IsTopologicalGroup G]` and `hρ : IsAdmissible ρ`.
- The definition `traceOrthogonalityIntegrand` and `traceOrthogonalityIntegrand_mk`: `hπ`, `hω`,
  `hωa : IsAdmissible ω` (so that `W^H` is finite-dimensional). Also for
  `traceOrthogonalityIntegrand_mk_smoothContragredient`.
- `integral_traceOrthogonalityIntegrand`: `hπ`, `hω`, `hωa`, the measure `μ`, and
  `hint : ∀ v₁ ℓ₁ v₂ ℓ₂, Integrable (orthogonalityIntegrand A hπ hω v₁ ℓ₁.val v₂ ℓ₂.val) μ`.
- `integral_traceOrthogonalityIntegrand_eq_zero`: the section data, `hπ`, `hω`, `hint`, `hcof`
  (every open subgroup of `G` contains a compact open subgroup), `IsAdmissible π`,
  `IsAdmissible ω`, `π.IsIrreducible`, `ω.IsIrreducible` and `hne : IsEmpty (π.Equiv ω)`.
  For tempered `π` the integrability `hint` is not proved here.
- `integral_traceOrthogonalityIntegrand_eq_formalDegree` and its `_of_mem` form (`π = ω`):
  the section data, `hA`, `hω`, `hcof`, `hsq : IsSquareIntegrableModCentralSubgroup A hA ω μ`
  and `hi : ω.IsIrreducible`; the `_of_mem` form adds `v ∈ fixedVectors ω H.toSubgroup`.

## Definitions

- `traceOrthogonalityIntegrand A hπ hω hωa H v ℓ : G ⧸ A → ℂ`, for `v : V` and an algebraic
  functional `ℓ` on `V`: the function whose value at `gA` is `ℓ(π(g) v) ψ^ω_H(g⁻¹)`
  (`traceOrthogonalityIntegrand_mk`). It is defined as the finite sum, over the basis
  `b = Module.finBasis ℂ (fixedVectors ω H.toSubgroup)` of `W^H`, of the Schur orthogonality
  integrands `orthogonalityIntegrand A hπ hω v ℓ (b i) (fixedFunctional ω _ H (b.coord i))`,
  which are already functions on `G ⧸ A`. Here `ψ^ω_H = traceCoefficient ω _ H`.

## Results

- `traceCoefficient_smoothContragredient`: for admissible `ρ`,
  `traceCoefficient (smoothContragredient ρ) _ H g = traceCoefficient ρ _ H g⁻¹`, i.e.
  `ψ^{ρ̌}_H(g) = ψ^ρ_H(g⁻¹)`.
- `traceOrthogonalityIntegrand_mk`: value `ℓ(π(g) v) ψ^ω_H(g⁻¹)` at `gA`;
  `traceOrthogonalityIntegrand_mk_smoothContragredient`: value `ψ^{ω̌}_H(g) ℓ(π(g) v)`, which is
  Waldspurger's integrand `ψ_H(g) ⟨π(g) v, v̌⟩` with `ψ_H = ψ^{ω̌}_H`.
- `integral_traceOrthogonalityIntegrand`: the integral over `G ⧸ A` is the finite sum
  `Σ_i I(v, ℓ, b_i, b_i^* ∘ e_H)` of Schur orthogonality integrals.
- `integral_traceOrthogonalityIntegrand_eq_zero` (**first case of p. 275**): if `π`, `ω` are
  irreducible admissible and not equivalent and the integrands are integrable, then
  `∫_{G/A} ψ^{ω̌}_H(g) ⟨π(g) v, ℓ⟩ dμ = 0`.
- `integral_traceOrthogonalityIntegrand_eq_formalDegree` (**second case of p. 275**): for `ω`
  irreducible and square integrable modulo `A`,
  `∫_{G/A} ψ^{ω̌}_H(g) ⟨ω(g) v, ℓ⟩ dμ = d(ω)⁻¹ ℓ(e_H v)`, with `d(ω) = formalDegree …` and
  `e_H v = Compact.averageMap ω _ H.1 H.2 v`.
- `integral_traceOrthogonalityIntegrand_eq_formalDegree_of_mem`: if `H` fixes `v`, the value is
  `d(ω)⁻¹ ℓ(v)`, i.e. `d(ω)⁻¹ ⟨v, v̌⟩`.

## Proof notes

- **`ψ^{ρ̌}_H(g) = ψ^ρ_H(g⁻¹)`.** Restriction to `V^H` is a linear equivalence
  `R : (V̌)^H ≃ (V^H)^*` (`smoothDualFixedRestriction_bijective`). For `m ∈ (V̌)^H` and
  `x ∈ V^H`, both `R(e_H ρ̌(g) m)(x)` and `R(m)(e_H ρ(g⁻¹) x)` equal `m(ρ(g⁻¹) x)`: averaging a
  functional does not change its value at an `H`-fixed vector
  (`Jacquet.map_averageMap_of_forall_eq`), and an `H`-fixed functional does not see the average
  of a vector (`Jacquet.smoothDualPairing_averageMap`). Hence `R` conjugates the compressed
  action of `ρ̌(g)` on `(V̌)^H` to the transpose of the compressed action of `ρ(g⁻¹)` on `V^H`,
  and the traces agree (`LinearMap.trace_conj'`, `LinearMap.trace_transpose'`).
- **Reduction to Schur orthogonality.** By `traceCoefficient_eq_sum`,
  `ψ^ω_H(g⁻¹) = Σ_i b_i^*(e_H ω(g⁻¹) b_i)`, a sum of coefficients `ℓ_i(ω(g⁻¹) b_i)` with the
  smooth functionals `ℓ_i = b_i^* ∘ e_H`. The integral of the finite sum is the sum of the
  integrals (`integral_finsetSum`, using `hint`).
- **The two cases.** If `π ≇ ω`, every summand vanishes by
  `orthogonalityIntegral_eq_zero_of_integrable`. If `π = ω`, by
  `orthogonalityIntegral_eq_formalDegree` the `i`-th summand is
  `d(ω)⁻¹ ℓ_i(v) ℓ(b_i)`, and `Σ_i ℓ_i(v) b_i = Σ_i b_i^*(e_H v) b_i = e_H v`
  (`Module.Basis.sum_repr`). If `H` fixes `v`, `e_H v = v` (`Compact.averageMap_id`).

## Relation to the Library

- `TraceCoefficientFamily` defines `ψ_H` for an arbitrary admissible `ρ` (Waldspurger's `ω̌`)
  and builds the family `φ_H = φ ψ_H`; this module supplies the integrals of `ψ_H` against
  coefficients needed to evaluate `π[φ]`.
- `SchurOrthogonality` supplies `I`, the orthogonality relations and the formal degree.
- No other Library declaration computes these integrals.

## Open obligations

- The Fourier inversion on the finite group `G¹A_G \ G`, the twist by unramified characters
  `χ`, the identity `d(ω ⊗ χ) = d(ω)`, the integrability `hint` for tempered `π`, and hence the
  scalar `P_ϕ(π)` and Proposition III.7.1 (ii), (iii).
