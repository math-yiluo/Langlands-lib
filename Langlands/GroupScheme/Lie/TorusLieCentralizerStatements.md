# Statements: tori centralizing Lie elements that commute with their tangent vectors

This module states two propositions and proves neither. Both are internal
statements, used by the semisimple-centralizer case (Case C) of the induction
proving `MaximalTorusParameterUnirationalStatement`. In both, "Lie centralizer"
means `Lie.elementCentralizerLie G Y`, the tangent submodule of the all-test
adjoint centralizer `Lie.elementCentralizer G Y`. "The tangent image of the
torus" means the vectors `Additive.ofMul (Lie.targetMap j k t)` for `t` in the
actual Lie kernel of the torus.

## `SemisimpleMaximalTorusLieCentralizerStatement`

Let `k : Type u` be an algebraically closed field. Let `G` be a group scheme over
`Spec k` that is smooth and affine with connected underlying space. Let
`j₀ : T₀ ⟶ G` be a maximal torus (`IsMaximalTorus j₀`), and let `Y` be a Lie
element of `G` that is geometrically semisimple (`Lie.IsSemisimpleElement G Y`).
Suppose every tangent vector of `T₀` maps into the Lie centralizer of `Y`. The
statement asserts that `SubgroupFunctor.range j₀ ≤ Lie.elementCentralizer G Y`:
over every test scheme, every point of `T₀` centralizes `Y`.

In positive characteristic, commuting with `Lie T₀` is weaker than being fixed by
`T₀`. A weight vector for a nonzero character divisible by `p` commutes with
`Lie T₀` but is not fixed by `T₀`. The semisimplicity hypothesis excludes this.
For example, in `𝔾a ⋊ 𝔾m` with weight `p`, the root vector commutes with
`Lie 𝔾m` but is nilpotent.

Intended route (not part of the statement). This follows the toral-subalgebra
argument of Borel, *Linear Algebraic Groups*, 2nd ed., Proposition 11.8,
combined with conjugacy of maximal tori. Let `𝔰` be the span of the tangent image
of `T₀` and `Y`. Iterated centralizers of a basis of `𝔰` give a smooth connected
subgroup whose Lie algebra contains `𝔰` centrally. The published
smoothness of semisimple centralizers (`Lie.semisimpleCentralizerSmooth`) and
semisimple centrality (`semisimpleCentrality`) apply at each step. The
published tangent-lift theorem `Lie.exists_tangent_lift_identityComponent_elementCentralizer`
applies over an algebraically closed field, where Cartan structure is proved.
It shows that a maximal torus `S` of that subgroup is maximal in `G` and that
`𝔰` lies in the tangent image of `S`. By maximal-torus conjugacy, `S` and `T₀` have
Lie algebras of equal dimension, so `Y` lies in the tangent image of `T₀`. Then
`Lie.range_le_elementCentralizer_of_tangent` gives the conclusion.

## `CharZeroTorusLieCentralizerStatement`

Let `k : Type u` be a field of characteristic zero. Let `G` be a group scheme over
`Spec k` that is smooth and affine. Let `j : T ⟶ G` be any homomorphism from a
commutative group scheme `T` with `IsTorus T.toGrp`, and let `Y` be any Lie element
of `G`. If every tangent vector of `T` maps into the Lie centralizer of `Y`, the
statement asserts that `SubgroupFunctor.range j ≤ Lie.elementCentralizer G Y`.

Intended route (not part of the statement). The preimage of the closed
centralizer of `Y` is a closed subgroup of `T`. It is smooth by Cartier's theorem
(`affineCartierSmooth`). Its Lie algebra is all of `Lie T`, so it is all of the
connected torus `T` (`Lie.isIso_of_surjective_targetMapLinear`).

## Provenance

Both statements are derived and internal. The first is the consequence of
Borel 11.8 and maximal-torus conjugacy described above. The second is the
characteristic-zero analogue, which needs no semisimplicity. Neither statement is
asserted in this form in the literature.
