# The cubic Lefschetz embedding over a field from the algebraically closed case

This module proves

```lean
theorem Langlands.AbelianScheme.PolarizedFiniteLevel.cubicFieldEmbedding_of_cubeSeparation
    (H : AlgClosedFieldAmpleCubeSeparationStatement.{u}) :
    CubicFieldEmbeddingStatement.{u}
```

It reduces the published Lefschetz statement for the canonical cubic bundle of an ordinary
polarized datum over an arbitrary field (`CubicFieldEmbeddingStatement`) to the published
separation statement over algebraically closed fields
(`Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement`, Mumford,
*Abelian Varieties*, §17). The premise `H` is the only hypothesis. Everything else is
proved from published results, including
`Langlands.AlgebraicGeometry.ProjectiveBundle.BaseChangeSectionBasis`.

The route follows the Markdown of `CubicFieldEmbeddingStatement`: base change to an
algebraic closure, flat base change of the global sections, and fpqc descent of the
closed immersion.

## Setup

`Langlands.GroupScheme.toAlgebraicClosure K : Spec (AlgebraicClosure K) ⟶ Spec K` is `Spec.map` of the algebra map.
`closureMap_flat_surjective` shows it is flat and surjective. This uses Mathlib's
`flat_and_surjective_SpecMap_iff`, together with the fact that a nonzero module over a
field is free and hence faithfully flat. Fix a datum `a` over `Spec K` with `0 < d`. Write
`p = a.abelian.X.hom`, `β = Langlands.GroupScheme.toAlgebraicClosure K`, `a' = a.pullback β` with structure morphism
`p' = a'.abelian.X.hom`, and `f = pullback.fst p β : X' ⟶ X`. Let `L = a.cubicBundle`.

## Steps

1. `Datum.separates_closure`. `H` applied to `AlgebraicClosure K`, `a'.abelian` and
   `a'.canonicalBundle` gives `SeparatesPointsAndTangents p' a'.cubicBundle`. The premise
   is ampleness of the canonical bundle, the first component of the published
   `canonicalCubicBundleAmple`. The conclusion holds because `a'.cubicBundle` is
   definitionally the cube in `H`. The published `SeparatesPointsAndTangents.of_iso`
   transports it along `a.cubicBundlePullbackIso β` to the pulled-back bundle `f^* L`.
2. `Datum.closure_comparison`. The published `cubicDirectImage` gives local freeness of
   `p_* L`, hence quasi-coherence. It also gives invertibility of
   `a.rigidificationBaseChangeMap β`, hence (published `isIso_cubicBaseChangeEvaluation`)
   of the comparison `baseChangeEvaluation` along `β`. These are the instance hypotheses
   of `baseChangeSectionBasis`.
3. `Datum.exists_mem_nonvanishingLocus_of_cubeSeparation`. Every point of `X` lies in the
   nonvanishing locus of some global section of `L`.
   - Take any `K`-basis `b` of `Γ(X, L)`. Let `U ⊆ X'` be the union of the
     trivialization opens of the pulled-back sections `f^* b_i`.
   - Every rational point `y` of `X'` lies in `U`. Otherwise all `f^* b_i` vanish along
     `y`, so every section of `f^* L` vanishes along `y`
     (`vanishesAlong_of_forall_pullbackSection`). That contradicts the base-point clause
     of step 1.
   - Since `X'` is of finite type over the algebraically closed field, `U = ⊤` (published
     `FiniteSeparating.eq_top_of_forall_rationalPoint_mem`).
   - Since `f` is surjective, a point `x` of `X` is `f x'`, and `x'` lies in some
     trivialization open of `f^* b_i`. By `mem_pullback_trivializationOpen_iff` and
     `lineBundleResidueOpenComparison`, `x` lies in the nonvanishing locus of `b_i`.
4. `Datum.epi_cubicEvaluationAdjoint_of_cubeSeparation`. The full cubic evaluation sends
   the pullback of the coefficient section `σ` to `σ` (`evaluationAdjoint_sectionPullback`).
   Step 3 and `epi_of_forall_mem_nonvanishingLocus` show it is an epimorphism.
5. `Datum.isClosedImmersion_relativeLinearSystemMap_of_cubeSeparation`. Fix a basis
   `b : Module.Basis (Fin (m + 1)) K Γ(X, L)` and a proof `hb` that its members have no
   common zero.
   - The pulled-back sections generate (`pullbackSections_generate f hb`). Every section of
     `f^* L` is a `linComb` of them (`exists_eq_linComb_pullbackSection`). So
     `isClosedImmersion_linearSystemMap_of_separates` and step 1 make
     `linearSystemMap p' _` a closed immersion.
   - The published `relativeLinearSystemMap_toPolynomial`, with the identity of
     `Spec (AlgebraicClosure K)`, identifies `relativeLinearSystemMap p' _` with it up to
     the isomorphism `RelativeProjectiveSpace.toPolynomial m (𝟙 _)`. Here
     `RelativeProjectiveSpace.map_id` shows that `RelativeProjectiveSpace.map m (𝟙 S)` is
     the identity.
   - The published `relativeLinearSystemMap_pullback` gives the commutative square
     `φ' ≫ RelativeProjectiveSpace.map m β = f ≫ φ`, where `φ` and `φ'` are the relative
     linear-system maps over `K` and over `AlgebraicClosure K`. Pasting the base-change
     square of `X'` with `RelativeProjectiveSpace.isPullback_map m β` (`IsPullback.of_right`)
     shows that this square is a pullback.
   - `RelativeProjectiveSpace.map m β` is a base change of `β`, hence surjective, flat and
     quasi-compact. `φ` is proper because `φ ≫ toBase = p` is proper and `toBase` is
     separated. So `isClosedImmersion_of_isPullback_of_fpqc` shows that `φ` is a closed
     immersion.
6. `cubicFieldEmbedding_of_cubeSeparation` combines steps 4 and 5 for every `P`, `K`,
   `g d n`, `0 < d` and datum.

## Scope

The theorem covers every universe, every field and every basis, exactly as quantified in
the published `CubicFieldEmbeddingStatement`. Its only premise is the separation
statement over algebraically closed fields. Together with an unconditional proof of that
statement, it yields the exact target of Task 7747
(`5e7c789a-8444-4b3e-a58a-fe10bd3c7b99`). This module alone is not that proof.

Worker 5655 wrote this module for Task 7747.
