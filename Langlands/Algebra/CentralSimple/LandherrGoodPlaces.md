# Finiteness of the places where given coordinates fail to be integral

Module: `Langlands.Algebra.CentralSimple.LandherrGoodPlaces`.

Let `F` be a number field, `A` an `F`-algebra with a finite basis `β`, and `IntAt`,
`BasisIntAt` as in `Langlands.Algebra.CentralSimple.LandherrIntegrality`.

- `finite_setOf_not_intAt`: for `a ∈ A`, the finite places `v` with `¬ IntAt β v a` form a
  finite set, contained in the finite union over the coordinates `β.repr a i` of their
  supports `HeightOneSpectrum.Support`.
- `finite_setOf_not_forall_intAt`: the same for finitely many elements `a j` at once (a
  finite union).
- `finite_setOf_not_basisIntAt`: the finite places at which the structure constants of `β`
  or the coordinates of `1` fail to be integral form a finite set, by the previous items
  applied to the products `βᵢ βⱼ` and to `1`.

## Provenance

Every element of a number field is integral at all but finitely many places. These
statements define the finite exceptional set of places in the proof of Landherr's theorem.
