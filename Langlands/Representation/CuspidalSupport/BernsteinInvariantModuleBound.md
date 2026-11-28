# A uniform module bound for Bernstein component invariants

Module `Langlands.Representation.CuspidalSupport.BernsteinInvariantModuleBound`.

Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026,
VI.7.1 (the quotient description of a component) and VI.10.5 (the finiteness paragraph
preceding the Proposition), printed pp.181 and 213 / PDF pp.187 and 219.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The uniform bound below is derived from the invariant-ring description, for use with
the product of component rings.

Let \(R\) be the algebra of regular functions on the unramified character torus of
the standard Levi of a cuspidal datum. Write \(W\) for its ambient component
group, realized as permutations of the characters. `BernsteinInvariantModuleBoundStatement`
asserts that \(R^V\) has an \(R^W\)-spanning family of length \(B\) for every
subgroup \(V\le W\). The inclusion is the scalar map and the same \(B\) works for
all cuspidal data in the standard family.

`InvariantFunctions.exists_spanningFamily_fixedSubalgebra` uses the action
of \(W\) on \(R\) by inverse precomposition. Its restriction to the preimage
of \(V\) in \(W\) has the same fixed points as the original permutations in
\(V\). The proof identifies both algebras with the corresponding
`FixedPoints.subalgebra` and transports `exists_spanningFamily_fixedPoints`
along these equalities. If \(d\) bounds the order of \(W\) and \(m\) bounds the
number of algebra generators of \(R\), the spanning family has length \(d^m\).

In `bernsteinInvariantModuleBound`, each standard Levi has a finite generating
set for its regular functions by `rationalUnramifiedRegularFunctions_finiteType`.
For the group order, `standardLevi_exists_finite_normalizer_representatives`
and `ComponentWeyl.rationalWeylGroup_card_le` give a bound for each Levi
independent of its cuspidal representation. The proof takes the maximum of
each bound over the finite set of standard Levi labels and applies the
invariant-module theorem.
