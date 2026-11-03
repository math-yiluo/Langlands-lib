# Actual cotangent pullback preserves equivariant character weights: proof

This module proves `CoordinateWeights.CotangentPullbackStatement` from
`Langlands.GroupScheme.Rational.CoordinateCotangentPullbackStatement` with the
theorem `CoordinateWeights.cotangentPullbackStatement`, whose type is exactly
`CotangentPullbackStatement.{u}`. Every universe `u` and every field
characteristic are retained, and no splitness, smoothness or finite-type
hypothesis is used. The statement is a derived functoriality consequence of the
augmentation/cotangent setup in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition (2015), §3.3, printed pp.107–108 / PDF pp.133–134; the proof below
is an implementation argument on the existing actual coordinate objects, not a
transcription of a printed proof.

The proof works with the existing objects only: the actual coordinate pullback
`pullback`, the full tensor augmentation `baseAugmentation G A` on
`A ⊗[k] O(G)`, the base-changed action `actionPullback b s` and its induced
cotangent action `cotangentAction b s`, the scalar extension
`cotangentBaseChange`, and the quotient pullback `cotangentPullback f` built from
`Ideal.mapCotangent`. The eigenconditions are those of `cotangentWeightSpace`,
tested on every commutative `k`-algebra `A` in universe `u` and every `A`-point
`s` of the commutative group scheme `S`, with the direct CGP character value
`Lie.characterValue χ s`.

## Base-changed pullback

For a coefficient algebra `A`, `basePullback A f : A ⊗[k] O(H) →ₐ[A] A ⊗[k] O(G)`
is the `A`-linear extension, via `AlgHom.liftEquiv`, of `includeRight ∘ pullback f`.
The module proves:

- `basePullback_tmul`: it sends `a ⊗ z` to `a ⊗ pullback f z`;
- `basePullback_coordinates`: its restriction to `O(H)` is `includeRight ∘ pullback f`;
- `basePullback_includeLeft`: it fixes the coefficient factor `A`;
- `baseAugmentation_basePullback`: for an actual group homomorphism `f : G ⟶ H`,
  composing with the full tensor augmentation of `G` gives that of `H`. On a pure
  tensor both sides are `a` times the image in `A` of the coordinate origin, and
  the existing law `pullback_origin` identifies the two origins;
- `basePullback_augmentation`: hence it maps the base-changed augmentation ideal
  of `H` into that of `G`.

`baseCotangentPullback A f` is the induced `A`-linear map on the base-changed
quotients `I_A/I_A²`, again by `Ideal.mapCotangent`.

## Two compatibilities

`cotangentBaseChange_cotangentPullback` shows that scalar extension of cotangent
classes commutes with pullback: representing a class by an augmentation element
`z`, both sides are the class of `1 ⊗ pullback f z`.

`actionPullback_basePullback` shows that for an equivariant morphism of the
underlying schemes (`IsEquivariant b c f`) the algebra maps
`actionPullback b s ∘ basePullback A f` and `basePullback A f ∘ actionPullback c s`
agree. By `Algebra.TensorProduct.ext_ring` it suffices to compare them on
`O(H)`. The left side is `actionCoordinates b s ∘ pullback f`, which by
`coordinates_comp` is the coordinate map of `b.act s' u_G ≫ f`, where `u_G` is the
universal point of `G` over `A ⊗ O(G)` and `s'` is `s` extended along
`includeLeft`. The right side is, by `pointCoordinates_naturality` and the
naturality `RelativeRoot.act_affineMap` of the actual action, the coordinate map
of `c.act s'' v`, where `s''` and `v` are the images of the extended acting point
and the universal point of `H` under `basePullback A f`. The helper
`basePullback_includeLeft` gives `s'' = s'`, and
`affineMap_basePullback_universal` gives `v = u_G ≫ f`. The equivariance
hypothesis at the test object `Spec (A ⊗ O(G))` then identifies the two points.

Passing to quotients, `cotangentAction_baseCotangentPullback` shows that
`cotangentAction b s ∘ baseCotangentPullback A f =
baseCotangentPullback A f ∘ cotangentAction c s` on every base-changed cotangent
class.

## The two conclusions

`cotangentPullback_mem_weightSpace`: if `q` lies in `cotangentWeightSpace c χ`,
then for every `A` and `s`,

```text
cotangentAction b s (cotangentBaseChange (cotangentPullback f q))
  = baseCotangentPullback A f (cotangentAction c s (cotangentBaseChange q))
  = baseCotangentPullback A f (χ(s) • cotangentBaseChange q)
  = χ(s) • cotangentBaseChange (cotangentPullback f q),
```

using the two compatibilities, the eigencondition of `q`, and `A`-linearity of
`baseCotangentPullback A f`. The first conjunct of the statement follows by
`Submodule.map_le_iff_le_comap`.

For an actual group-scheme isomorphism `e : G ≅ H` with `e.hom` equivariant,
`isEquivariant_inv` shows that `e.inv` is equivariant from `c` to `b`, by
cancelling the monomorphism `e.hom` on the underlying schemes. The cotangent
pullbacks of `e.hom` and `e.inv` are the forward maps of the existing linear
equivalences `cotangentPullbackEquiv e` and `cotangentPullbackEquiv e.symm`, so
they are injective. `cotangentSupport_subset` shows that an injective equivariant
cotangent pullback carries a nonzero χ-eigenvector to a nonzero χ-eigenvector, so
the target support is contained in the source support. Applying it to `e.hom` and
to `e.inv` gives `cotangentSupport_eq_of_iso`, the second conjunct. Support keeps
the existing meaning: characters with a nonzero cotangent eigenvector, with the
zero character allowed only when it occurs.

The final theorem `cotangentPullbackStatement` introduces the data of the
statement and combines these two results.
