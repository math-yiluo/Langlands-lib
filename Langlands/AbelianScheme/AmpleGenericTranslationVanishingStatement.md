# No nontrivial generic translation period for the zeros of sections of an ample generated bundle

`Langlands.AbelianScheme.AmpleGenericTranslationVanishingStatement.{u}` is a
`Prop`-valued definition, not a proof. Let `K : Type u` be algebraically closed,
`A : AbelianScheme (Spec (CommRingCat.of K))`, and `N : LineBundle A.X.left`.
Assume `N.IsAmple` and assume that for each rational point there is a global
section of `N` not vanishing at that point. If `x` is a rational point, `U` a
nonempty open in `A.X.left`, and for every rational `y` in `U` and every global
section `σ` of `N` one has

```text
VanishesAlong N y.left σ  →  VanishesAlong N (x * y).left σ,
```

then `x = 1`.

Here the rational points are morphisms `Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X`,
with multiplication from the abelian group law; `1` is the unit point. Membership
in `U` is tested at the image of `IsLocalRing.closedPoint K`. `VanishesAlong`, from
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`, means that the
pullback of the section is zero. The hypothesis is one-way and uses a *common*
open for all sections. It does not assert that `N` itself separates points or
that any particular section has a reduced divisor.

## Provenance and role

This is a derived input for a proof of Lefschetz's theorem. In Mumford,
*Abelian Varieties*, Oxford University Press (1970), §17, printed pp.163–164
(PDF pp.86–87 of `mumford-abelian-varieties-full-scan`), failure of `|3D|` to
separate two points is used to force translation invariance of the support of a
reduced divisor in `|D|`. The argument then excludes a nontrivial finite
translation period using the quotient by the translations and an Euler
characteristic count. The Lean proposition takes a different intermediate
hypothesis: it uses *all* sections of the ample, generated `N`, but only tests
vanishing over `U`. The intended application takes `N = L ⊗ L`, with sections of
`L³` constructed as `τ_a^*σ ⊗ τ_{(a a)⁻¹}^*s` for a fixed section `s` of `L`;
the theorem of the square identifies the tensor product bundle with the cube.
Failure of point separation by the cube then gives the displayed implication on
a nonempty open. The statement isolates what is needed after that step, without
requiring a reduced divisor of `L`.

## Mathematical justification (not formalized here)

The two evaluations at `y` and `xy` have codimension-one kernels on `H⁰(A,N)` by
the no-base-point hypothesis. Inclusion makes them equal, so the complete
linear system morphism has equal values at `y` and `xy`. The morphism is defined
everywhere (over an algebraically closed field a nonempty closed base locus
would have a rational point). The rational points of the nonempty open are
schematically dense in the integral variety, so the morphism is invariant under
`τ_x`. Each fibre has finitely many rational points: a positive-dimensional
proper fibre would have both a trivial and an ample restriction of `N` since
`N` is the pullback of `𝒪(1)`. The fibre over the image of the unit contains the
powers of `x`, so `x` has finite order. The complete morphism factors through
the finite étale quotient `π : A → A/⟨x⟩`. Pulling back `𝒪(1)` from the factored
map gives a bundle `M` with `π^*M ≅ N`; it is ample by finite surjective
reflection of ampleness. All the generating sections of the complete linear
system descend (they are pullbacks of the coordinates of projective space), so
`h⁰(N) = h⁰(M)`. On the other hand, higher cohomology vanishes for these ample
bundles and the isogeny Euler characteristic count gives
`h⁰(N) = deg(π) · h⁰(M)`. Since there is a section nonzero at the unit, this
forces `deg(π) = 1`, i.e. `x = 1`.
