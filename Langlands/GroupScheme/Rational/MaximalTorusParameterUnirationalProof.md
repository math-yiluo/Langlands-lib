# Proof: unirationality of the actual maximal-torus parameter scheme

Author: Worker 1420.

`maximalTorusParameterUnirational : MaximalTorusParameterUnirationalStatement.{u}` proves the
published target of module `Rational/MaximalTorusParameterUnirationalStatement`, at an
arbitrary universe `u`, with the statement and its imports unchanged. Take any field
`k : Type u` (finite, imperfect, any characteristic), any smooth connected affine group `G`
over `k`, any maximal torus `j₀ : T₀ ⟶ G`, and any actual `Q` and `q : G.X ⟶ Q` with
`IsMaximalTorusParameter j₀ q`. The theorem gives `IsUnirational k Q` for this same `Q`. It
adds no premise: no infinitude, perfectness, reductivity, splitness, characteristic or
rationality assumption.

## The Lean proof

The theorem is one application of the published conditional theorem
`maximalTorusParameterUnirational_of_isogeny_data` (module
`Rational/MaximalTorusConjugatorCaseC`) to four published proofs:

- `maximalTorusIsogenyReduction : MaximalTorusIsogenyReductionStatement` (Case B, module
  `Rational/MaximalTorusIsogenyReduction`). It gives a flat, surjective, quasi-compact,
  universally open homomorphism `φ : G → G'` onto a smooth connected affine group `G'` with
  a maximal torus `j₀'`. The map `φ` reflects torus normalizers, and `G'` has Lie dimension
  at most that of `G`. Either every point of `G'` normalizes `j₀'`, or `G'` has a noncentral
  geometric semisimple Lie element.
- `maximalTorusConjugacy : MaximalTorusConjugacyStatement` (module
  `Absolute/MaximalTorusConjugacyProof`): maximal tori are conjugate over an algebraically
  closed field.
- `maximalTorusBaseChange : MaximalTorusBaseChangeStatement` (module
  `Torus/MaximalBaseChangeProof`, Milne, *Algebraic Groups* (2017), Theorem 17.82): a torus is
  maximal exactly when its base change to a field extension is maximal.
- `semisimpleCentralizerConjugationData semisimpleMaximalTorusLieCentralizer
  charZeroTorusLieCentralizer maximalTorusBaseChange : SemisimpleCentralizerConjugationDataStatement`
  (generic conjugation data for Case C). This comes from the companion module
  `Rational/MaximalTorusConjugatorCaseCData`, which is submitted with this proof (see its
  Markdown). It is applied to the published proofs `semisimpleMaximalTorusLieCentralizer`
  (module `Lie/TorusLieCentralizerProof`), `charZeroTorusLieCentralizer` (module
  `Lie/CharZeroTorusLieCentralizerProof`) and `maximalTorusBaseChange`.

## The implemented parametrization of `Q`

The published reductions that `maximalTorusParameterUnirational_of_isogeny_data` composes
build the parametrization as follows.

1. *Case C* (`semisimpleCentralizerConjugatorReduction_of_data`). Suppose `G` has a
   noncentral geometric semisimple Lie element. The generic conjugation data give:
   - a field `K` over `k` whose rational function fields are rational function fields
     over `k`;
   - a smooth connected affine closed subgroup `H` of `G_K` of smaller Lie dimension (the
     identity component of the centralizer of the generic Lie element, or of a prime power
     of it in characteristic `p`);
   - a point of `G_K` over an algebraically closed field `Ω`, with dense image in `G`, that
     conjugates `T₀` into `H`.

   A maximal torus of `H` (`maximalTorusExistence`), conjugacy of maximal tori over `Ω`
   (`maximalTorusConjugacy`) and the base-change statement (`maximalTorusBaseChange`) turn
   these into the transfer data `IsTorusConjugatorTransfer` of
   `MaximalTorusGenericConjugatorInduction`.
2. *Case split and induction* (`maximalTorusParameterUnirational_of_cases`,
   `maximalTorusConjugatorReduction_of_cases`, `maximalTorusGenericConjugator_of_reduction`).
   Case B maps `G` onto `G'`. In the first alternative of Case B, `G'` normalizes its maximal
   torus, and the published `hasGenericTorusConjugator_of_normalizer_eq_top` applies. In the
   second, Case C applies to `G'`. A strong induction on the Lie dimension,
   over all fields at once, then produces a generic torus conjugator
   (`HasGenericTorusConjugator j₀`) for `j₀`, lifted along `G → G'`
   (`HasGenericTorusConjugator.of_hom`). Such a conjugator consists of:
   - a finite coordinate type `n : Type u`;
   - a scheme `X` over `k` with a flat, surjective, quasi-compact morphism
     `π : X → Spec k(x_i : i ∈ n)`;
   - a morphism `g : X → G.X` with dense range;
   - the descent condition `TorusConjugateDescends j₀ π g`: test points of `X` with equal
     images under `π` give points of `G` that differ by a point of the torus normalizer.
3. *Descent to `Q`* (`maximalTorusParameterUnirational_of_genericConjugator`,
   `IsMaximalTorusParameter.isUnirational_of_torusConjugateDescends`). The supplied
   parameter map `q` identifies points of `G` that differ by a normalizer point (the
   all-test fiber relation of `IsMaximalTorusParameter`). So `g ≫ q` descends along the
   fpqc covering `π`, which is an effective epimorphism, to a point
   `e : Spec k(x_i) → Q` over `k` with `π ≫ e = g ≫ q`. The point `e` has dense range,
   because `g` has dense range and `q` is surjective and continuous.
4. *Spreading out* (`HasDenseRationalFunctionFieldPoint.isUnirational`). `Q` is locally of
   finite type over `k` by the parameter predicate. So the dense point `e` extends to an
   actual morphism over `k` from a nonempty open subscheme of the affine space `𝔸(n; Spec k)`
   to `Q` whose underlying image is dense. This is exactly the published predicate
   `IsUnirational k Q`, for the supplied `Q` itself.

The supplied `Q` is never replaced by a quotient `G/N(T₀)` or by any other model. Its only
use is through the descent property of `q` given by `IsMaximalTorusParameter`.
