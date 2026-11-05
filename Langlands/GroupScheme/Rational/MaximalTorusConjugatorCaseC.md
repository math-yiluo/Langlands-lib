# Assembly of the generic semisimple-centralizer case

Author: Worker 1420.

This internal, derived module reduces Case C,
`SemisimpleCentralizerConjugatorReductionStatement` of
`MaximalTorusConjugatorReductionCases`, to one statement about generic conjugation data. It
also states the resulting reduction of the target `MaximalTorusParameterUnirationalStatement`.
The reductions are conditional on two published but unproved Library propositions, which
appear as explicit hypotheses: `MaximalTorusConjugacyStatement` and
`MaximalTorusBaseChangeStatement`. No new statement is proved here except these reductions.

## The data statement

`SemisimpleCentralizerConjugationDataStatement.{u}` quantifies over a field `k : Type u`, a
group scheme `G` over `k` that is smooth and affine with connected underlying space, and a
maximal torus `j₀ : T₀ → G` (`IsMaximalTorus j₀`). It assumes
`HasNoncentralGeometricSemisimpleElement G`, and asserts that there are:

- a field `K : Type u` with a `k`-algebra structure such that
  `ReducesRationalFunctionFields (algebraBaseMap k K)` holds;
- a group scheme `H` over `K` that is smooth and affine with connected underlying space;
- a homomorphism `i : H → G_K` into `G_K = (GroupScheme.baseChange (algebraBaseMap k K)).obj G`,
  with `IsClosedSubgroup i` and `Lie.dimension H < Lie.dimension G`;
- an algebraically closed field `Ω : Type u` with a `K`-algebra structure;
- a point `c : Over.mk (algebraBaseMap K Ω) → G_K`.

These are required to satisfy two conditions:

1. The point of `G` over `k` corresponding to `c` under the published
   `baseChangePointsEquiv` has dense range.
2. For every scheme `V` over `K`, every `y : V → Over.mk (algebraBaseMap K Ω)` and every
   point `t` of `G_K` over `V`: if `t` lies in the base change of the all-test range of
   `j₀`, then `(y ≫ c) * t * (y ≫ c)⁻¹` lies in the all-test range of `i`.

The intended instance takes `K` to be the function field of the Lie algebra, as an affine
space over `k`, with the algebra structure `rationalFunctionFieldAlgebra`. In that case
`ReducesRationalFunctionFields` follows from
`reducesRationalFunctionFields_rationalFunctionFieldOver` and
`algebraBaseMap_rationalFunctionField`. `H` is the identity component of the centralizer of
`X^[p^r]` for the generic Lie element `X`. `c` is a generic conjugator moving the torus into
`H`, and `Ω` is an algebraic closure of its field of definition. This module does not
construct these data.

## The reductions

`semisimpleCentralizerConjugatorReduction_of_data` proves that
`MaximalTorusConjugacyStatement`, `MaximalTorusBaseChangeStatement` and
`SemisimpleCentralizerConjugationDataStatement` together imply
`SemisimpleCentralizerConjugatorReductionStatement`. Given the data:

- the published `maximalTorusExistence` gives a maximal torus `j : T → H`;
- `exists_torusConjugator_of_conj_mem_range` gives `h₁ : Over.mk (algebraBaseMap K Ω) → H`
  such that `p = (h₁ ≫ i) * c` conjugates the base change of `j₀` onto `j ≫ i` over every test
  scheme;
- `isTorusConjugatorTransfer_of_translate` turns this and the density of `c` into
  `IsTorusConjugatorTransfer (algebraBaseMap k K) j₀ j i (Over.mk (algebraBaseMap K Ω)) p`.
  `Spec Ω → Spec K` is flat and surjective by the published `TorusExistence` lemmas. It is
  quasi-compact because it is affine.

These are exactly the data of `HasSmallerTorusConjugatorReduction j₀ (Lie.dimension G)`.

`maximalTorusParameterUnirational_of_isogeny_data` combines this with
`maximalTorusParameterUnirational_of_cases`. It proves that `MaximalTorusIsogenyReductionStatement`,
`MaximalTorusConjugacyStatement`, `MaximalTorusBaseChangeStatement` and
`SemisimpleCentralizerConjugationDataStatement` imply
`MaximalTorusParameterUnirationalStatement`.

## Provenance

The module is derived from the helper modules `MaximalTorusConjugatorReductionCases`,
`MaximalTorusGenericConjugatorInduction` and `MaximalTorusConjugatorGeometricConjugacy`. It
also uses the published `maximalTorusExistence`, `TorusExistence.flat_algebraBaseMap`,
`TorusExistence.surjective_algebraBaseMap` and `baseChangePointsEquiv`. The data statement
is an internal reformulation of the semisimple-centralizer step of the dimension induction
modeled on SGA 3, Exposé XIV, Théorème 6.1. No literature statement is formalized.
