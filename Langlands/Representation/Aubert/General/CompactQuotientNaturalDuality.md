# Natural integral duality of normalized induction from a compact quotient

Author: Worker 937.

This module specializes `Langlands.Induction.exists_integralDualEquiv_of_section`
(module `Induction/CompactQuotientSmoothDuality`) to normalized induction along
an actual semidirect decomposition `P = M ⋉ U`
(`IsSemidirectDecomposition P M U`). It feeds the interfaces `IsIntegralDuality`
and `IsNaturalIntegralDuality` of module `Aubert/General/NaturalIntegralDuality`
(Worker 1402). It is the all-smooth counterpart of the Library's
`exists_natural_of_compactSpace` (module
`Aubert/General/RationalInductionDualityAssembly`), which covers admissible
objects only.

## Provenance

Internal. The module states no definition or proposition taken from a source.
The mathematical content is Renard, *Représentations des groupes réductifs
p-adiques* (2026 version), III.2.7 (printed p. 78, PDF p. 84) for a compact
quotient, normalized as in VI.1.2; see `CompactQuotientSmoothDuality.md`.

## Statements

Let `G` be a locally compact nonarchimedean group, `P = M ⋉ U` an actual
semidirect decomposition with `U` closed, `P` closed, a continuous Levi
projection `h.projection : P →* M`, and `P \ G` compact. Write `χ` for the half
character `HaarModulus.closedHalfCharacter U hU P h.le_normalizer`.

- `isIntegralDuality_of_compactSpace`: let `δ : P → ℝ≥0` satisfy
  `χ q * χ q = δ q`. Let `μ` be a measure on a subgroup `K` that is positive on
  open neighbourhoods of `1` and whose integral is right invariant on locally
  constant functions `φ` with `φ(q x) = δ(q) φ(x)`. Then
  `IsIntegralDuality h hU K μ` holds: for every smooth `A`, an equivalence
  `(i A)~ ≅ i(A~)` characterized by `⟨ℓ, f⟩ = ∫_K ⟨(E ℓ)(k), f(k)⟩ dμ`.
- `exists_isNaturalIntegralDuality_of_compactSpace`: assume further that `G` is
  T2 with a Borel measurable structure, that `P` is locally compact, that `G` is
  unimodular (`hG`), and that the modular character of `P` equals the
  restricted Haar modulus of conjugation on `U` (`hδ`). Then there are a
  measure `μ` on `⊤ : Subgroup G` and a natural isomorphism
  `C : i.op ⋙ D ≅ D ⋙ i` with `IsNaturalIntegralDuality h hU ⊤ μ C`.

The hypotheses `hG` and `hδ` are those of `exists_natural_of_compactSpace`.
No admissibility is assumed.

## Proof

`isIntegralDuality_of_compactSpace`: by `isIntegralDuality_of_twistEquiv` it
suffices to produce, for each smooth `A`, the twisted equivalence of
`exists_integralDualEquiv_of_section` with `m = h.projection`. Its section is
the Levi inclusion `Subgroup.inclusion h.levi_le : M →* P`. It is continuous
(`continuous_inclusion`) and `h.projection` is the identity on it
(`projection_levi`). The kernel of `χ` is open by
`HaarModulus.isOpen_ker_closedHalfCharacter`.

`exists_isNaturalIntegralDuality_of_compactSpace`: the Library's
`Induction.exists_compactQuotient_measure` gives a measure on `⊤` positive near
`1` with the scalar property for `δ = ` the modular character of `P`.
`closedHalfCharacter_mul_self` and `hδ` give `χ q * χ q = δ q`. The first
theorem gives `IsIntegralDuality`, and `exists_isNaturalIntegralDuality`
assembles it into the natural isomorphism.

## Scope

For a parabolic `P` of a reductive group, the remaining inputs are those of
`exists_natural_of_compactSpace`: compactness of `P \ G`, unimodularity of `G`
and the identification of the modular character. This module proves none of
them.
