# Actual pullback of finite Harris Rosati solutions

This internal compatibility construction uses the existing positive Harris
integral order, its finite integer basis, its restricted positive auxiliary
left involution, and the actual Rosati equations from
`HarrisIntegralRosatiEquations`. The arithmetic types have universe zero;
the base schemes have an independent arbitrary universe.

Let `b : S' → S` be any scheme morphism and `B` a supplied abelian scheme
over `S`. Both `B` and `b*B` retain specified dual-existence and geometry
witnesses, inverse Poincaré line bundles and evaluations. All named tensor,
Picard-zero pullback, universal base-change and dual comparison premises
remain explicit. For the supplied actual map `λ : B → D(B)`, write
`λ_b = b*(λ) ≫ β.hom`, where `β` is the existing canonical
`dualAbelianBaseChangeIso`. Thus `λ_b` is exactly
`dualAbelianBaseChangeMap`, with the specified changed dual presentation.

The private equation lemma pulls back an actual equality
`f ≫ λ = λ ≫ dual(g)`. Functoriality first gives the pulled-back
composition equation. The published `dualAbelianBaseChangeNaturality`
theorem rewrites `b*(dual(g)) ≫ β.hom` as
`β.hom ≫ dual(b*(g))`. Reassociation gives
`b*(f) ≫ λ_b = λ_b ≫ dual(b*(g))`. The proof uses actual homomorphism
equalities throughout.

`IntegralRosatiEquations.baseChange` applies this argument to every element
of the order. The action on `b*B` is the existing
`baseChangeOrderAction b B a`, with no new action or involution chosen.
`IntegralRosatiBasisEquations.baseChange` applies the same argument only
to the existing integer basis.

`IntegralRosatiTupleEquations.baseChange` applies it with `f = r_k`
and `g = ∑ j, c_jk • r_j`, where `c_jk` is the coefficient of `b_j`
in the involution of `b_k`. The published actual endomorphism pullback
is a ring homomorphism, so it preserves that finite sum and its integer
scalar multiples. The resulting tuple is exactly the existing
`integralActionSolutionsBaseChange`. Its unit and ordered multiplication
relations are already preserved by that construction.

`integralRosatiSolutionsBaseChange` combines this tuple map with its proved
Rosati preservation to construct a map between the two actual subtypes of
finite action solutions satisfying Rosati for `λ` and `λ_b`.
No additivity premise for dualization is needed: each equation is pulled
back directly rather than extended from basis values to every order element.

The provenance is internal functoriality, the published actual canonical
dual naturality theorem, and integer additivity of the published endomorphism
pullback. This supplies compatibility of the finite equations along every
base morphism. It asserts neither reflection under pullback nor existence of
actions, duals, polarizations, representing loci or an ambient moduli scheme.
It does not identify ordinary isomorphism classes with rational-isogeny
classes or prove the parent CM representability proposition.
