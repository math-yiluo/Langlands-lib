# Natural integral duality of normalized induction on all smooth objects

Lean module: `Langlands.Representation.Aubert.General.NaturalIntegralDuality`,
namespace `Langlands.Aubert.General`.

## Provenance

Internal infrastructure for Renard 2026, VI.9.6 (printed p.201–202, PDF p.207–208). The proof
of the first Theorem of VI.9.6 uses the statement "l'induction normalisée commute avec la
dualité" for all smooth representations, not only admissible ones. Renard's source for this is
III.2.7 (printed p.78, PDF p.84): for a closed subgroup `H` of `G` and a smooth
representation `W` of `H`, `Ind_H^G(W~)` is the smooth dual of `ind_H^G(W ⊗ δ_{H\G})`, via
the integral over `H\G` of the coefficient pairing. When `P\G` is compact and induction is
normalized by `δ_P^{1/2}`, this becomes a natural isomorphism `(i A)~ ≅ i(A~)`.

The Library already has the admissible form: `IsUniformIntegralDuality` and
`exists_natural_of_isUniformIntegralDuality`
(`Aubert/General/RationalInductionDualityReduction.lean`). `exists_natural_of_compactSpace`
(`Aubert/General/RationalInductionDualityAssembly.lean`) proves it from compactness of `P\G`,
unimodularity of `G`, and the modular character of `P`. This module states the same integral
characterization for every smooth `A`, with the admissibility hypothesis removed. The
predicates are interfaces. The module does not prove that they hold.

## Contents

The setting is a locally compact nonarchimedean group `G` with subgroups `P`, `M`, `U`, a
semidirect decomposition `h : IsSemidirectDecomposition P M U` and a closedness proof `hU` for
`U`. Write `i` for `normalizedInductionFunctor h hU` and `D` for the smooth contragredient.
`Induction.eval P _ f k` is the value at `k` of an induced function `f`, and
`smoothDualPairing` is the pairing between a smooth dual and its representation.

`IsIntegralDuality h hU K μ` is defined for a subgroup `K` of `G` and a measure `μ` on `K`.
It says that for every smooth representation `A` of `M` there is an equivalence of
representations `E : (i A)~ ≃ i(A~)` with

`⟨ℓ, f⟩ = ∫_K ⟨(E ℓ)(k), f(k)⟩ dμ(k)` for all `ℓ ∈ (i A)~` and `f ∈ i A`.

The definition is `IsUniformIntegralDuality` without the hypothesis `A.IsAdmissible`.

`IsNaturalIntegralDuality h hU K μ C` is defined for a natural isomorphism

`C : i.op ⋙ D ≅ D ⋙ i`

of functors `(SmoothRep ℂ M)ᵒᵖ ⥤ SmoothRep ℂ G`. It says that for every smooth `A`, the
component `C.hom.app (op A) : (i A)~ ⟶ i(A~)` satisfies the same formula:
`⟨ℓ, f⟩ = ∫_K ⟨(C ℓ)(k), f(k)⟩ dμ(k)`.

`exists_isNaturalIntegralDuality h hU K μ hdual` proves that `IsIntegralDuality h hU K μ`
implies the existence of a `C` with `IsNaturalIntegralDuality h hU K μ C`.

`isIntegralDuality_of_twistEquiv h hU K μ hE` proves `IsIntegralDuality h hU K μ` from an
equivalence for every smooth `A` in the form produced by the Library's
`Induction.exists_integralDualEquiv_of_pos`. Here the source is the smooth contragredient of
`smoothInduced P (inducingRepresentation h hU A)`. The target is `smoothInduced P` of the
twist of `A~ ∘ h.projection` by `closedHalfCharacter U hU P h.le_normalizer`. The integral
formula is the same.

## Proof

For `isIntegralDuality_of_twistEquiv`, apply the Library's `exists_functorEquiv_of_twistEquiv`
to each `A`. It rewrites the two representations as `(i A)~` and `i(A~)` and keeps the
integral formula.

For `exists_isNaturalIntegralDuality`, choose the equivalence `E A` for every `A`. Then `C` is `NatIso.ofComponents` of the
isomorphisms `SmoothRep.mkIso (E A)`, and the integral formula holds by construction.
Naturality is the argument of the Library's `exists_natural_of_isUniformIntegralDuality`.
Fix `f : A ⟶ B` and `ℓ ∈ (i B)~`. Both sides of the naturality square are elements of
`i(A~)`. Write the right-hand side as `E_A` applied to its `E_A`-preimage, and compare that
preimage with `D(i f) ℓ` as functionals on `i A`. Their values at `x ∈ i A` are equal. The
integral formulas for `E_B` and `E_A` turn them into `∫_K ⟨(E_B ℓ)(k), (i f x)(k)⟩ dμ(k)` and
`∫_K ⟨(f~ (E_B ℓ)(k)), x(k)⟩ dμ(k)`. These integrands agree by definition of `i f` and of the
contragredient map `f~`.
