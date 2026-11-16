# Fppf local lifting of independent monomials

This internal derived module applies the published canonical pullback construction `AutomorphicAction.fppfQuotientPointLift` to the exponent projection supplied by `RelativeRootScalingTorus`. For any finite linearly independent family of integer weights and any tuple of global units on a test scheme over an arbitrary affine base, it supplies a flat, surjective, locally finitely presented refinement with unit coordinates whose monomials equal the prescribed units after restriction. The construction includes the zero ring and nonaffine test schemes.

Let `R` be a commutative ring, let `I` and `J` be finite types, and let
`m : J → I → ℤ` be linearly independent over `ℤ`. For a test scheme `V`
over `Spec R` and units `c : J → Γ(V, O)ˣ`, the construction
`splitTorus.exponentUnitsLift R m hm V c` has type
`AutomorphicAction.FppfQuotientPointLift (splitTorus.exponentTorusProjection R m)
((splitTorus.pointsEquiv J V).symm c)`.
Its underlying scheme is the pullback of the exponent projection along the
point corresponding to `c`. Its fields retain the covering test object,
the projection to `V`, the lifted torus point, the commutative square, and
flatness, surjectivity and local finite presentation of that projection.
These properties follow by base change from
`splitTorus.exponentTorusProjection_fppf`.

`splitTorus.exponentUnitsLift_equation` computes the lifted point in the
specified unit-coordinate model. If `L` is the constructed lift, then for
every `j : J`,

```text
∏ i, splitTorus.pointsEquiv I L.cover L.lift i ^ m j i
  = splitTorus.unitsRestrict J L.projection c j.
```

Here `unitsRestrict` pulls global units back along the projection.
The implemented proof first uses `exponentTorusProjection_points`, then the
retained commutative square, then naturality of `pointsEquiv` and its
inverse law. It does not assume the covering test scheme is affine.

`splitTorus.exponentUnitsLiftCover` packages the projection as a singleton
`Scheme.fppfPrecoverage` cover of the underlying scheme of `V`.
`splitTorus.exists_fppf_exponent_units` forgets the selected pullback and
retains the existential form: there are a test scheme `W`, a morphism
`b : W ⟶ V` that is flat, surjective and locally of finite presentation,
and units `t : I → Γ(W, O)ˣ` such that every specified monomial equals the
pullback of the corresponding unit `c j`.

The provenance is the categorical pullback construction and the projection
geometry proved in the imported modules. This is an internal derived API,
with no additional source theorem asserted here. Linear independence is
the only condition on the integer weights; the image lattice need not be
saturated. Consequently the cover is asserted to be fppf, and no smoothness
claim is made. The module supplies a local unit-lifting ingredient for
relative root-scaling arguments; it does not assert the reductive-isogeny
rigidity theorem.
