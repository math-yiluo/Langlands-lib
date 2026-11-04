# Real evaluation of actual cocharacters and their integral Weyl sums

This is an internal construction for the actual-point route to
`DerivedSmoothRealAnnihilationStatement`. It is derived from the published
cocharacter point-evaluation and actual normalizer action APIs, without an
additional assertion from the literature.

Let `k` be a field in any universe, `T` a commutative group scheme over
`Spec k`, `G` a group scheme over `Spec k`, and `i : T.toGrp ⟶ G` an
actual homomorphism. Fix an ambient group homomorphism
`f : rationalPoints G →* Multiplicative ℝ` and an actual point
`z ∈ Gm(k)`.

The additive homomorphism `cocharacterRealEvaluation i f z` sends an integral
cocharacter `ν` to the additive real value of `f(i(ν(z)))`. Its construction
composes `evalPoint z` with the additive form of the actual point
homomorphism `f ∘ rationalPoints.map i`. Consequently addition of
cocharacters gives addition of real values.

The theorem `cocharacterRealEvaluation_normalizingAut` proves invariance under
every actual normalizing point. The imported
`groupHom_cocharacterAut_comp` identifies the transported cocharacter with
the original cocharacter followed by the actual inner automorphism.
`rationalPoints_map_innerIso` identifies that point map with literal
conjugation. The image under `f` is unchanged because its codomain is
commutative.

If the underlying scheme map of `i` is a monomorphism, invariance descends to
the existing action of the actual quotient
`relativeWeylGroup i = N(k)/Z(k)`, by lifting each quotient element to a
normalizing point. If that quotient has a `Fintype` instance, additivity
then gives

`eval(relativeWeylCocharacterSum i ν) = |relativeWeylGroup i| · eval(ν)`.

The integral Weyl sum is exactly the one defined in
`Langlands.GroupScheme.Rational.WeylPositiveCocharacter`. Its index is a
group, so its finite cardinality is nonzero. Thus zero evaluation of that
sum forces zero evaluation of `ν`. Two corollaries supply sufficient
conditions: the integral Weyl sum itself is zero, or its evaluation at `z`
inside the actual ambient point group has a positive power equal to one.
For the latter, applying `f` to the power equation and taking its additive
real value yields a nonzero natural multiple equal to zero.

These statements do not require a split torus, smoothness, reductivity,
an open kernel, or a topology. They do not establish reflection existence,
the torsion condition for any particular derived-group torus, or
annihilation of all algebraic derived rational points. Those remain
separate structural obligations of the parent argument.
