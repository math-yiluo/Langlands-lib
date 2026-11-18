# Statement: flat square-zero deformations of diagonalizable groups

`Langlands.GroupScheme.DiagonalizableSquareZeroDeformationStatement.{u}` is a
proposition. This file states the deformation assertion; it does not prove it.

For a commutative ring `R : Type u`, an ideal `J` with `J ^ 2 = ⊥`, a finitely
generated abelian group `N : Type u`, and a flat affine group scheme `G` locally
of finite presentation over `Spec R`, set `r : Spec (R/J) ⟶ Spec R` to be the
quotient morphism and `D := RelativeMultiplicativeType.diagonalizable (Spec R) N`.
Every specified isomorphism

```text
f₀ : r*G ≅ r*D
```

lifts to an isomorphism `f : G ≅ D` with `(GroupScheme.baseChange r).map f.hom =
f₀.hom`. The conclusion preserves the specified reduced homomorphism, rather than
merely asserting that `G` is diagonalizable.

The source is Brian Conrad, *Reductive group schemes* (2014), registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
p.289, the paragraph beginning “To be precise” in the proof of Theorem B.3.2(2).
PDF and printed page numbers agree. That paragraph takes a square-zero ideal in
an arbitrary ring, an affine fppf group, a finitely generated abelian group, and
a specified isomorphism of its reduction with the corresponding diagonalizable
group, and asserts that this isomorphism lifts.

Here “affine fppf group” is expressed by `IsAffineHom G.X.hom`, `Flat G.X.hom`,
and `LocallyOfFinitePresentation G.X.hom`. A group scheme has an identity section
over its base, so its structure morphism is surjective. Affineness is
quasi-compactness as well, so these hypotheses have the source's faithfully flat
finite-presentation meaning. No smoothness, localness, noetherianity, or
torsion-freeness of `N` is assumed.

The reduced target is written as `r*D`. Set
`e := RelativeMultiplicativeType.diagonalizableBaseChangeIso r N`, the published
isomorphism `r*D ≅ D_(Spec (R/J))(N)`. Thus the source's isomorphism
`g₀ : r*G ≅ D_(Spec (R/J))(N)` corresponds to `f₀ := g₀ ≪≫ e.symm`;
conversely, the displayed `f₀` gives `g₀ := f₀ ≪≫ e`. The lifting equation then
implies `(GroupScheme.baseChange r).map f.hom ≫ e.hom = g₀.hom`.
This expresses exactly the specified lift in the source using the existing
comparison isomorphism. The comparison comes from the definition of `D_S(N)`
as the base change of `Spec ℤ[N]`, together with the base-change composition
isomorphism. Equality of isomorphisms is determined by equality of their
homomorphisms.

This assertion is a substantial prerequisite for complete local deformation
arguments: its iteration gives diagonalizability over successive infinitesimal
quotients. The statement itself includes neither that iteration nor algebraization
of compatible homomorphisms over a complete ring. Conrad's proof invokes
cohomological deformation theory. In particular, the separate smooth-target
homomorphism lifting statement cannot be applied directly with target `D(N)`
when `N` has torsion.

Worker 356 supplied the initial unaccepted draft. Worker 701 checked it against
the cited source and expanded the base-change correspondence.
