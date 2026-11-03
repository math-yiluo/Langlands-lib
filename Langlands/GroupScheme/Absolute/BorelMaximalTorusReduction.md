# Maximal tori and Borel subgroups, assuming Borel conjugacy

Worker 1418.

This module contains derived internal infrastructure for the published targets
`BorelMaximalTorusStatement` and `MaximalTorusConjugacyStatement`. The results
in the field section are unconditional. The two final theorems are conditional:
they take `BorelConjugacyStatement` as an explicit hypothesis, and the second one
also takes solvable-group conjugacy of maximal tori as a hypothesis. Neither
input is proved here. The published targets and their imports are unchanged.

## Unconditional results over an arbitrary field

Everything in this section works over an arbitrary field `k : Type u`. The field
need not be algebraically closed or perfect, and the characteristic is arbitrary.

`BorelExistence.isAdmissible_of_isTorus`: a closed torus `j : T ⟶ G` is an
admissible subgroup in the sense of the published `BorelExistence.IsAdmissible`.
In other words, it is a closed subgroup that is smooth, connected and solvable.
Smoothness and connectedness come from `IsTorus.smooth` and
`IsTorus.connectedSpace` (module `Torus.HeightExistence`). Solvability comes from
the published `isSolvableGroupScheme_of_commutative`.

`maximalToriLieInBorels`: if `G` is affine and locally of finite type over `k`,
then `G` satisfies the published property `MaximalToriLieInBorels G`. So every
given maximal torus `j` of `G` belongs to a Borel pair `(i, j)`. The torus is
admissible by the previous lemma. The published
`BorelExistence.exists_isBorelSubgroup_containing` gives a Borel `i : B ⟶ G` and a
factor map `f` with `f ≫ i = j`. With the maximality of `j`, this gives the pair.

`exists_isBorelPair`: under the same hypotheses on `G`, some Borel pair exists. The
module `Torus.HeightExistence` gives a maximal torus of `G` over `k`
(`exists_isMaximalTorus`), and `maximalToriLieInBorels` places it in a Borel.

`IsBorelPair.of_subgroupConjugate`: let `(i, j)` be a Borel pair, `i' : B' ⟶ G` a
Borel subgroup, `g` a rational point of `G` and `φ : B ≅ B'` an isomorphism with
`i ≫ int(g) = φ ≫ i'`. Then `(i', j ≫ int(g))` is a Borel pair. The torus stays
maximal after composing with the inner automorphism
(`IsMaximalTorus.comp_iso`). If `f ≫ i = j`, the factor map is `f ≫ φ`.

`BorelSubgroupsContainMaximalTori G` is the property that every Borel subgroup
`i : B ⟶ G` belongs to a Borel pair `(i, j)` for some maximal torus `j` of `G`. It
is a per-group form of the target `BorelMaximalTorusStatement`. Defining this
property does not assert that any group satisfies it.

`BorelSubgroupsContainMaximalTori.of_conjugate`: let `G` be affine and locally of
finite type over `k`. Suppose any two Borel subgroups of `G` are conjugate by a
rational point, in the form used by the second component of
`BorelConjugacyStatement`. Then `BorelSubgroupsContainMaximalTori G` holds. The
proof takes the Borel pair `(i₀, j)` from `exists_isBorelPair`. For a given Borel
`i`, it conjugates `i₀` onto `i` and transports the pair with
`IsBorelPair.of_subgroupConjugate`.

## Conditional assemblies

`borelMaximalTorusStatement_of_borelConjugacy`: `BorelConjugacyStatement.{u}`
implies `BorelMaximalTorusStatement.{u}`. Fix an algebraically closed field `k`
and a smooth affine connected `G`. Smoothness supplies the
`LocallyOfFiniteType` instance. The previous theorem then applies to the
conjugacy component of the hypothesis. The Borel existence component of
`BorelConjugacyStatement` is not used.

`maximalTorusConjugacyStatement_of_borelConjugacy`: `BorelConjugacyStatement.{u}`,
together with conjugacy of maximal tori in smooth affine connected solvable groups
over algebraically closed fields, implies `MaximalTorusConjugacyStatement.{u}`. It
is the published `maximalTorusConjugacyStatement_of_borel_inputs` with its
containment hypothesis discharged by `maximalToriLieInBorels`.

## Literature

The route is Milne, *Algebraic Groups* (2017), the paragraph after
Definition 17.12, printed p.355 (one-based PDF p.371). Every maximal torus, being
connected and solvable, lies in a Borel. So some Borel subgroup is part of a
Borel pair, and since any two Borel subgroups are conjugate (Theorem 17.9), every
Borel subgroup is. Milne takes the existence of a maximal torus for granted. Here
it is the internal theorem `exists_isMaximalTorus`. Milne's proof of Theorem 17.10
on the same page places maximal tori in Borels in the same way. That is the
containment input that `maximalTorusConjugacyStatement_of_borelConjugacy`
discharges.

This contribution does not complete the host task: a published proof of
`BorelConjugacyStatement` is still needed.
