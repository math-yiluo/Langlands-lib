# Cartier perfectness along a principal polarization

Author: Worker 195. This is an internal construction from the published
`FiniteWeilCartierPerfectness`, the actual integer-torsion functor, and
`FiniteWeilAlongHom`. It adds no external mathematical input.
The exact proposition `RelativeDualKernelCharacterBijectiveStatement`
remains an explicit theorem dependency, named `duality`.

Let `S` be a quasi-separated scheme and `A/S` an actual abelian scheme.
Retain the seven tensor/Picard constructor propositions, a dual-scheme
witness, the actual dual geometry, an inverse Poincare line bundle, and
its evaluation isomorphism. These determine exactly the dual abelian
scheme `DA` used by `FiniteWeilAlongHom`. Let `n` be a natural number
invertible in the global sections of `S`.

For an actual isomorphism `lam : A → DA`,
`finiteWeilAlongIsoCartierIso` constructs a natural isomorphism of
abelian-group-valued functors on all schemes over `S`:

`T ↦ A[n](T)  ≅  T ↦ Hom_T(A[n]_T, Gm_T)`.

The domain is the actual torsion point group, written additively. The
target is the published Cartier-character functor, with its canonical
base-change presentation. `finiteWeilAlongIsoCharacterHomIso` composes
with the published canonical comparison to obtain the displayed
actual-Hom presentation. This is a statement about group-scheme
characters over each test scheme, including nonreduced tests.

The construction first applies `CommGroupScheme.torsionFunctor` to the
actual isomorphism `lam`. The helper `GroupScheme.additivePointsIso`
postcomposes points with the resulting torsion isomorphism, using its
actual inverse to establish the inverse identities and its
homomorphism law for additivity. Associativity of composition proves
naturality. Composition with `finiteWeilCartierIso` then gives the
claimed isomorphism.

`finiteWeilAlongHomTorsionMap_eq_torsionMap` proves that the torsion
map already used by the pairing agrees with the torsion functor's map.
Both have the same composite with the monic torsion inclusion.
Consequently the component formula is exactly
`y ↦ dualTorsionCharacter n (lam[n](y))`, with no change of sign.
The evaluation lemma identifies its canonical `mu_n`-valued evaluation
at `x` with the existing `finiteWeilAlongHomValue lam n x y`.
Thus this is Cartier perfectness of the already constructed
`e_n(x, lam[n](y))`, with the primal point first.

`finiteWeilPrincipalCartierIso` specializes to the exact published
`IsPrincipalPolarization` predicate. Its additional `square` and
`universality` arguments are retained as inputs of that predicate.
The proof uses the predicate's `IsIso lam` conjunct to apply the
preceding construction. The polarization conjunct is part of this
specialization's hypotheses; no positivity argument is needed for the
isomorphism once `lam` is invertible. The final evaluation lemma states
the same original root-valued pairing formula directly for this
principal-polarization specialization.

This construction does not discharge relative Cartier bijectivity,
construct the dual geometry, prove alternation, or assert numerical
rank. It proves no perfectness claim for an arbitrary nonprincipal
polarization, and makes no identification with all abstract
homomorphisms between groups of test-scheme points.
