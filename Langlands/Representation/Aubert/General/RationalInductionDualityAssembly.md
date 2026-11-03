# Rational natural induction duality from quotient compactness and the modulus

Module `Langlands.Representation.Aubert.General.RationalInductionDualityAssembly`,
namespace `Langlands.Aubert.General`.

## Scope

This module reduces the proof target
`Langlands.Aubert.General.RationalPointFamily.RationalNaturalInductionDualityStatement`
(task `2137e0ce-8d32-43f5-b4ed-79824b68585f`) to two published proof targets:

- `Langlands.BruhatTits.DynamicParabolicQuotientCompactStatement`: the right-coset
  space of the rational points of a dynamic parabolic is compact;
- `Langlands.Aubert.General.RationalPointFamily.RationalParabolicModulusStatement`:
  the rational-point group is unimodular, and Mathlib's modular character of an
  actual standard parabolic `P = M ⋉ U` is the restricted Haar modulus of
  conjugation on `U`.

Both statements appear as hypotheses of the final theorem. The module does not
prove them. It adds no other hypothesis.

## Provenance

Internal: both theorems assemble published Library results and the companion
module `RationalInductionDualityReduction`. The published inputs include
`IsSemidirectDecomposition.isClosed_levi` from `RationalInvolutivityReduction` and
the Bruhat-function measure and integral duality of
`Langlands.Representation.Induction.CompactQuotientDuality` (Worker 805). The
underlying mathematics is the compact-picture duality `i(σ)∨ ≅ i(σ∨)` through
`⟨ℓ, f⟩ = ∫ ⟨ℓ(k), f(k)⟩ dk` (Casselman, lecture notes *Introduction to
representations of p-adic groups*, Chapter III, section 1, Proposition III.1.1),
with the integral taken against a Bruhat-function measure on all of `G` instead
of Haar measure on a maximal compact subgroup.

## `exists_natural_of_compactSpace`

Let `G` be a locally compact, Hausdorff, nonarchimedean group with its Borel
structure, and let `h : IsSemidirectDecomposition P M U` with `U` and `P` closed
and the Levi projection continuous. Assume `P \ G` is compact, `G` is unimodular
(`Measure.modularCharacter g = 1` for all `g`), and the modular character of `P`
equals `HaarModulus.closedRestrictCharacter U hU P`. Then normalized induction
has a natural family of isomorphisms `i(A)∨ ≅ i(A∨)` on admissible `A`, in the
form of the target's conclusion.

Proof.

1. `Induction.exists_compactQuotient_measure` gives a measure `meas` on the top
   subgroup `⊤` of `G`. It is positive on open neighbourhoods of `1`, and on
   locally constant functions `φ` with `φ(qx) = Δ_P(q) φ(x)` its integral is
   invariant under right translation.
2. The induction character squares to `Δ_P`: by `closedHalfCharacter_mul_self`
   it squares to the restricted modulus, which equals `Δ_P` by hypothesis.
3. `M` is closed (the published `IsSemidirectDecomposition.isClosed_levi` of
   `Langlands.Representation.Aubert.General.RationalInvolutivityReduction`), so it
   has cofinal compact open subgroups (`compactOpenCofinal_of_isClosed`).
4. For each admissible `A`, smooth induction of its inducing representation is
   admissible (`smoothInduced_inducingRepresentation_isAdmissible`).
   `Induction.exists_integralDualEquiv_of_pos`, with `K = ⊤`, the measure `meas`,
   `δ = Δ_P` and the facts of steps 1-3, then gives an equivalence characterized
   by the integral over `⊤`. `exists_functorEquiv_of_twistEquiv` puts it in the
   form used by `IsUniformIntegralDuality`. The measure does not depend on `A`, so
   `IsUniformIntegralDuality h hU ⊤ meas` holds.
5. `exists_natural_of_isUniformIntegralDuality` gives the natural family.

## `RationalPointFamily.rationalNaturalInductionDuality_of_compact_of_modulus`

`DynamicParabolicQuotientCompactStatement` and `RationalParabolicModulusStatement`
imply `RationalNaturalInductionDualityStatement`, at all universe levels `u`, `v`.

Proof. Introduce the data of the target: the local field `k`, the connected
reductive `G`, the maximal split torus `i`, the instances on `G(k)` with its point
topology, the generic cocharacter `ν`, `StandardCocharacterStatement`, the set `I`
of simple roots, closedness of `U` and `P`, and continuity of the projection. The
modulus statement applied to the same data gives unimodularity of `G(k)` and the
modular character of `P`. `compactSpace_leftQuotient_parabolic` gives compactness
of `P \ G(k)`. `P` is locally compact because it is closed. After equipping
`G(k)` with its Borel σ-algebra, `exists_natural_of_compactSpace` gives the
conclusion. The functor `F` of the target is
`normalizedInductionFunctor` of the decomposition
`isSemidirectDecomposition_of_standardCocharacterStatement`, at universes
`u` and `max (u + 1) v`, which is the functor in step 5.
