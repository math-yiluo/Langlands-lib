# Composition of constant terms along standard parabolics

Module `Langlands.Global.AdelicConstantTermComposition`. Main results:
`Langlands.Global.StandardParabolicFamily.constantTerm_constantTerm` and its statement form
`Langlands.Global.ConstantTermCompositionStatement`, proved by
`Langlands.Global.constantTermComposition`.

## Statement

Let `𝓕 : StandardParabolicFamily F G` be a compatible standard parabolic family of a connected
reductive group `G` over a number field `F`, in an arbitrary universe `u`. Let `R, Q` be standard
indices, that is, sets of simple relative roots. Let `f : ContinuousRationalFunctions F G` be a
continuous complex function on `G(𝔸)` that is invariant under left translation by `G(F)`. Then

`𝓕.constantTerm R (𝓕.constantTerm Q f) = 𝓕.constantTerm (R ∩ Q) f`

as functions on `G(𝔸)`. Here `𝓕.constantTerm J φ g = ∫_{U_J(F)\U_J(𝔸)} φ(u g) du` is the
Library's constant term (`AdelicGroupPoints.subgroupConstantTerm`). It is computed on chosen
representatives with the normalized quotient measure, which is a probability measure here because
the quotient is compact. The index `R ∩ Q` is written `⟨R.1 ∩ Q.1, _⟩` in the statement and
`𝓕.interIndex R Q` in the proof. It is the index of the standard parabolic `P_R ∩ P_Q`.

The statement is pointwise and needs no growth hypothesis. The inner function `𝓕.constantTerm Q f`
is in general not `G(F)`-invariant. The theorem is stated for continuous `G(F)`-invariant `f`. It is
not stated for arbitrary locally integrable functions on `P₀(F)\G(𝔸)`.

## Generic part (namespace `Langlands.Global.ConstantTermComposition`)

For subgroup functors `U, V` of `G` with closed adelic points and compact rational quotients:

- `IsRationalInvariant F G V φ`: `φ` is invariant under left translation by the principal image
  of `V(F)` in `V(𝔸)`.
- `descendedIntegrand`: for such `φ` and `g`, the function `[v] ↦ φ(v g)` on `V(F)\V(𝔸)`.
  `descendedIntegrand_out` evaluates it on chosen representatives, and
  `continuous_descendedIntegrand` proves continuity for continuous `φ`.
- `integral_integral_out_eq`: if `U ≤ V` and `V` normalizes `U`, then for continuous `φ` that is
  invariant under `V(F)`,
  `∫_{V(F)\V(𝔸)} ∫_{U(F)\U(𝔸)} φ(u v g) du dv = ∫_{V(F)\V(𝔸)} φ(v g) dv`,
  with chosen representatives and normalized measures on both sides. This generalizes the
  Library's `AdelicSubgroupPoints.integral_normalizedConstantTerm_eq_of_isNormalizedBy`, which
  requires `G(F)`-invariance. The proof is the same. It applies the Library's
  `LeftCosetSpace.integral_compactSubgroupAverage` to the descended integrand, and checks the
  conjugation condition with `adelicNormalizerConj` and
  `measurePreserving_rationalQuotientAutomorphism`. Only `V(F)`-invariance of `φ` is used.
  `rationalSubgroup_count_isHaarMeasure'` restates a private Library helper: counting measure on
  the discrete rational subgroup is Haar.
- `average U φ g`: the integral `∫_{U(F)\U(𝔸)} φ(u g) du` on chosen representatives, as in
  `subgroupConstantTerm`.
- `average_eq_self`: if `φ` is invariant under all of `U(𝔸)`, then `average U φ = φ`, because the
  measure is a probability.
- `average_subgroup_mul`: if `φ` is `U(F)`-invariant, then `average U φ` is left
  `U(𝔸)`-invariant. The proof uses right-translation invariance of the normalized quotient
  measure (`measurePreserving_rightTranslate_of_compactRationalQuotient`).
- `average_normal_mul`: if `U` normalizes `W` and `φ` is left `W(𝔸)`-invariant, then so is
  `average U φ`. The proof writes `u w g = (u w u⁻¹) u g`.

## Standard part (namespace `Langlands.Global.StandardParabolicFamily`)

Write `U_J = rad(J) = SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)` and `I = R ∩ Q`.

- `exists_mul_of_mem_radical_inter`: every point of `U_I(𝔸)` is a product of a point of `U_R(𝔸)`
  and a point of `U_Q(𝔸)`. This is `StandardConstantTerm.standardUnipotent_inter_subset_mul` at
  the adele ring, transported along the Library identification
  `range_radical_eq_standardUnipotent`.
- `constantTerm_constantTerm`. Put `φ = C_Q f` and `ψ = C_R φ`. Then:
  1. `φ` is continuous (`continuous_normalizedConstantTerm`), left `U_Q(𝔸)`-invariant
     (`normalizedConstantTerm_subgroup_mul`), and invariant under the rational points of `U_I`.
     The last holds because `U_I` normalizes `U_Q`
     (`normalizedConstantTerm_rationalNormalizer_mul`, `radical_isNormalizedBy_of_le`). Since
     `U_R ≤ U_I` (`radical_le_of_le`), `φ` is also invariant under the rational points of `U_R`.
  2. `ψ` is left `U_R(𝔸)`-invariant (`average_subgroup_mul`). It is also left
     `U_Q(𝔸)`-invariant (`average_normal_mul`), since `U_R ≤ U_I` normalizes `U_Q`. Hence `ψ` is
     left `U_I(𝔸)`-invariant by the product decomposition.
  3. So `ψ = C_I ψ` (`average_eq_self`). Next, `C_I ψ = C_I φ` by `integral_integral_out_eq`
     with `U = U_R ≤ V = U_I`. Finally, `C_I φ = C_I f` by the Library's nested identity
     `constantTerm_constantTerm_of_le` for `I ≤ Q`.

## Provenance

Joseph Bernstein and Erez Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §7.3 (p. 214). Bernstein and Lapid
state `CT_{P₁ ∩ P₂} = CT_{P₁} ∘ CT_{P₂}` for all standard `P₁, P₂`, with the reason
`U_{P₁}U_{P₂} = U_{P₁∩P₂}`. They use it for the projections `Σ_{Q ⊆ P} (−1)^{dim 𝔞_Q^P} CT_Q`
onto the cuspidal parts. The source states the identity on `L¹_loc(P₀(F)\G(𝔸))`. This module proves
it pointwise for continuous `G(F)`-invariant functions. In the application, constant terms are
applied to smoothed automorphic functions, which satisfy these hypotheses. The module does not
prove the Harish-Chandra decomposition, cuspidality of its components, or any `L²` statement.
