# Surjectivity of affine-chart Weil restrictions

Author: Worker 185.

This module supplies the second local input for the affine-atlas step in
Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Lemma 5.10, printed pp.17–18 (registered source
`conrad-2011-weil-grothendieck-adelic-points`): restriction of scalars of a
surjective étale quasi-affine scheme along a finite locally free extension is
surjective. The proof below is a standard point-lifting argument written for
this Library; it is not copied from the source.

## Algebra

`Langlands.Algebra.nonempty_algHom_of_isArtinianRing` states: let `C` be a
formally smooth `B`-algebra and `D` an Artinian `B`-algebra. If `C` has a
`B`-algebra map to every residue field `(D ⧸ nilradical D) ⧸ I` of the reduced
quotient (indexed by its maximal spectrum), then `C` has a `B`-algebra map to
`D`. The reduced Artinian ring `D ⧸ nilradical D` is the product of these
fields (`IsArtinianRing.equivPi`), so the given maps assemble into a map to it;
the nilradical of an Artinian ring is nilpotent, and formal smoothness
(`Algebra.FormallySmooth.lift`) lifts the map through it.

## Points

`nonempty_ringPoint_of_isAlgClosed` states that if `Y` is locally of finite
type over `Spec R`, `L` is an algebraically closed field with an `R`-algebra
structure, and `y` is a point of `Y` lying over the image of the closed point
of `Spec L`, then `Y` has an `L`-valued point over `Spec R`. The proof chooses a
point of the base change `Y ×_{Spec R} Spec L` over `y`, uses that this base
change is locally of finite type over `Spec L` and hence a Jacobson space to
find a closed point, and takes the `L`-point of that closed point
(`pointOfClosedPoint`); the closed points have residue field `L` because `L`
is algebraically closed.

`exists_isAlgClosed_point` states that every point `t` of `Spec A` is the image
of the closed point of `Spec K` for some algebraically closed field `K` with an
`A`-algebra structure: take an algebraic closure of the residue field at `t`.

## Surjectivity

Let `B` be a finite projective algebra over an arbitrary commutative ring `A`.
`affineChartWeilRestriction_surjective` states that for a scheme `Y` over
`Spec B` that is locally of finite type, quasi-affine, étale and surjective,
the structure morphism of `affineChartWeilRestriction A B Y` to `Spec A` is
surjective.

Proof: given a point `t` of `Spec A`, choose an algebraically closed `K`
hitting it. The ring `D = B ⊗[A] K` is finite over `K`, hence Artinian, and
every residue field of its reduced quotient is finite over `K`, hence equal to
`K` and algebraically closed. By surjectivity of `Y` choose, for each of these
finitely many residue fields, a point of `Y` over the corresponding point of
`Spec B`. Quasi-affineness supplies an affine open `U` of `Y` containing these
finitely many points (`Picard.exists_isAffineOpen_of_finite_of_quasiAffine`).
The coordinate ring of `U` is étale, hence formally smooth over `B`; the
previous results give `B`-algebra maps from it to each residue field and then
to `D`. Through `affineSchemePointEquiv` and `affineWeilRestrictionPointEquiv`
this is a `K`-point of `affineWeilRestriction A B U` over `Spec A`, which maps
by the chart inclusion `affineChartWeilRestrictionι` into the glued scheme; its
closed point lies over `t`.

The module claims no étaleness or representability statement.
