# Finite support of the local components of idele cohomology in degree two

Let `E / F` be an extension of number fields and `J_E` the idele group of
`E`, with the published Galois representation `relativeIdeleRepresentation F E`.
For finite places `w | v`, the published `ideleLocalMap v w n` sends
`Hⁿ(Gal(E/F), J_E)` to `Hⁿ(Gal(E_w/F_v), E_wˣ)`: restriction along
`decompositionHom v w`, followed by the `w`-coordinate. This module proves
that a class in degree `2` has a nonzero local component at only finitely
many finite places `v` of `F`. It assumes that each
`H²(Gal(E_w/F_v), E_wˣ)` is finite with at most `[E_w : F_v]` elements. That
assumption is part of local class field theory. In the intended use it comes
from the image conditions of a local invariant family (the published
`InvariantFamily.RelativeImages`). This module does not prove it.

Only finite places and degree `2` are treated. Nothing here concerns the
infinite places, other degrees, or the injectivity of the sum of the local
maps.

## The support of a class

`ideleLocalSupport c`, for `E / F` normal and `c ∈ Hⁿ(Gal(E/F), J_E)`, is the
set of finite places `v` of `F` such that `ideleLocalMap v w n c ≠ 0` for some
finite place `w` of `E` with `w.asIdeal.LiesOver v.asIdeal`.

## Finiteness facts

- `finite_setOf_ideleCoordinate_not_mem_localUnits`: for an idele `x` of `E`,
  only finitely many finite places `w` have a coordinate
  `ideleCoordinate w x` outside the published valuation units
  `localUnits w`. The finite adele of `x` and that of `x⁻¹` are integral at
  all but finitely many places. Where both are integral, the coordinate and
  its inverse have valuation at most `1`, so the coordinate has valuation
  `1`.
- `finite_setOf_ramificationIdx_ne_one`: only finitely many finite places `w`
  of `E` have ramification index `w.asIdeal.ramificationIdx (𝓞 F) ≠ 1`. By
  Mathlib's `not_dvd_differentIdeal_iff` and
  `Ideal.ramificationIdx_eq_one`, a prime that does not divide the different
  ideal of `𝓞 E` over `𝓞 F` has ramification index `1`. The different ideal
  is nonzero, so it has finitely many prime factors.
- `subsingleton_setOf_liesOver`: a finite place `w` of `E` lies over at most
  one finite place of `F`, because the place below is `w.asIdeal ∩ 𝓞 F`.

## Local vanishing

- `mem_cocycles₂_of_injective`: let `ι : A ⟶ B` be a morphism of
  representations that is injective on carriers. A function `f` into `A` is
  a 2-cocycle if `ι ∘ f` is a 2-cocycle of `B`.
- `ideleLocalMap_H2π_eq_zero`: let `E / F` be Galois and let `w | v` have
  ramification index `1`. Assume that `H²(Gal(E_w/F_v), E_wˣ)` is finite with
  at most `[E_w : F_v]` elements. Let `f` be a 2-cocycle of `J_E` whose values
  all have `w`-coordinate in `localUnits w`. Then `ideleLocalMap v w 2` kills
  the class of `f`. The local cocycle of `E_wˣ` is the image of a cocycle of
  the published `localUnitsRepresentation v w` under the published inclusion
  `localUnitsInclusion v w`. By the published `isZero_H2_localUnits`, the
  class of that unit cocycle is zero.

## Finite support

- `finite_setOf_ideleLocalMap_ne_zero`: let `E / F` be Galois and assume, at
  every pair of finite places `w | v`, that `H²(Gal(E_w/F_v), E_wˣ)` is finite
  with at most `[E_w : F_v]` elements (hypotheses `hfin` and `hcard`). Then
  `ideleLocalSupport c` is finite for every
  `c ∈ H²(Gal(E/F), J_E)`. Represent `c` by a 2-cocycle `f`. `Gal(E/F)` is
  finite, so `f` has finitely many values. Let `T` be the finite set of
  places `w` where some value of `f` has a coordinate outside the units,
  together with the ramified places. If `v ∈ ideleLocalSupport c`, witnessed by `w | v`,
  then `w ∈ T`, by the local vanishing theorem. So `ideleLocalSupport c`
  lies in the image of `T` under "the place below", which is finite.
- `finite_setOf_ideleLocalMap_choice_ne_zero`: the same conclusion for a
  chosen place `wf v` over each finite place `v`: the set of `v` with
  `ideleLocalMap v (wf v) 2 c ≠ 0` is finite.

## Sources and provenance

Milne, *Class Field Theory* (v4.03, 2020), Chapter VII §2, Proposition 2.5(b)
and its proof, printed pp. 205–206 (PDF pp. 214–215), writes `J_E` as the
directed union of the groups `J_{E,S}`. For `S` containing the ramified
primes, he computes the cohomology of `J_{E,S}` by Shapiro's lemma, and the
factors at `v ∉ S` vanish by Chapter III, Proposition 1.1. Hence
`Hʳ(G, J_E) = ⊕_v Hʳ(G_v, E_vˣ)` for `r > 0`, a direct sum.

This module proves only the finiteness part of that statement in degree `2`,
for the local maps at finite places. It works with a single cocycle instead
of a direct limit. The finitely many values of the cocycle lie in one group
`J_{E,S}` (the set `T` above), and at the remaining places the vanishing of
`H²(Gal(E_w/F_v), U_w)` from the published `LocalUnitVanishing` module
applies. That vanishing needs the cardinality hypothesis, as recorded there.
The cocycle-level argument and the form of the hypotheses are internal.
