# Rigidity through the actual torsion-point configuration

For an abelian scheme `A` over `Spec K`, `torsionRationalPoints A n` sends
every element of the actual level module to its underlying morphism
`Spec K → A.X.left` over `Spec K`. The structure-map equality is the
commuting triangle of the section as a morphism in the over category.
This construction requires no full-level structure or algebraic closedness.

Given a supplied morphism `i : A.X.left → ProjectiveSpace K m` over `Spec K`,
`torsionProjectivePointConfiguration i hi` composes these actual point
morphisms with `i`.

`torsionProjectivePointConfiguration_hyperplaneBound` converts a supplied
bound on `TorsionHyperplaneSections i f n` for every nonzero homogeneous
linear polynomial `f` into `RationalPointHyperplaneBound` for this
configuration. A nonzero linear functional determines a nonzero homogeneous
linear polynomial through `linearFormPolynomialEquiv`; its injectivity and
the injectivity of subtype coercion prove nonzeroness. The two incidence
subtypes then agree by definition.

Over an algebraically closed field, `PolarizedIso.fixes_torsionRationalPoints`
uses the published equality of the action on the full geometric level with
the identity. Evaluating that equality on each level element and taking its
underlying section proves equality of actual rational-point morphisms.

`PolarizedIso.eq_refl_of_hom_eq_id` works over any base scheme. If the
underlying scheme endomorphism of a polarized automorphism is the identity,
extensionality for the over-category and group-object morphisms makes its
abelian-scheme homomorphism the identity. Isomorphism extensionality and
proof irrelevance for the polarization and level equations then identify
the actual polarized automorphism with `PolarizedIso.refl`.

`PolarizedIso.hom_eq_id_of_torsionConfiguration` considers a polarized
automorphism preserving the ordered full level, a supplied monomorphism
`i` over the field, a hyperplane count bound `q`, and the strict inequality
`(m + 1) * q < n^(2*g)` at positive level. It also assumes a supplied
coordinate linear equivalence `e` with the actual equivariance equation
`hom α.abelianIso.hom ≫ i = i ≫ linearAction K m e`. The conclusion is
equality of the original underlying scheme endomorphism with the identity.

The supplied full level makes the actual torsion module finite and gives
its cardinality `n^(2*g)`. Choose a finite-type structure for that module,
convert the cardinal inequality, transfer the hyperplane bound and the
fixedness of the actual torsion points, and apply the monic-embedding
configuration rigidity theorem. That theorem makes the ambient action a
scalar-unit identity on the actual projective scheme and cancels `i`.

`PolarizedIso.eq_refl_of_torsionConfiguration` combines this scheme identity
with `PolarizedIso.eq_refl_of_hom_eq_id`. Under the same hypotheses it
concludes equality of the actual polarized automorphism with the identity.

`PolarizedIso.eq_refl_of_cubicTorsionHyperplaneBound` uses the exact
published `CubicTorsionHyperplaneBoundStatement` as a supplied premise.
It retains that statement's positive dimension, polarization index and
level, the nonzero image of the level in `K`, a closed immersion over
`Spec K`, its pullback identification with the actual cubic bundle,
and its nondegeneracy against every nonzero linear polynomial.
The supplied strict inequality is

```
(m + 1) * (6^g * d * g! * n^(2*g - 2)) < n^(2*g).
```

The theorem applies the supplied count statement to obtain the uniform
hyperplane bound, uses that a closed immersion is a monomorphism, and
applies `PolarizedIso.eq_refl_of_torsionConfiguration` with the supplied
equivariant lift. Its conclusion is again equality of the actual polarized
automorphism with the identity. No proof of the count statement or of the
strict numerical inequality is supplied by this adapter.

This is an internal adapter of the published full-level cardinality and
geometric-fibre detection results to actual projective configuration
rigidity. It neither constructs the embedding or equivariant linear lift
nor proves a geometric hyperplane bound or a numerical range. Those remain
necessary inputs before this result supplies actual finite-level
automorphism rigidity in the ordinary moduli construction.
