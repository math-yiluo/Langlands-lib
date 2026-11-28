# Integrality at a finite place of coordinates in a finite-dimensional algebra

Module: `Langlands.Algebra.CentralSimple.LandherrIntegrality`.

Let `F` be a number field, `A` an `F`-algebra with a finite basis `β`, and `v` a finite place
of `F`.

- `finite_setOf_exists_one_lt`: for a finite set `s ⊆ F`, only finitely many finite places
  make some element of `s` non-integral (a finite union of the finite supports
  `HeightOneSpectrum.Support`).
- `finite_setOf_valuation_ne_one`: a nonzero element of `F` is a unit at all but finitely
  many finite places (the supports of `c` and `c⁻¹`).
- `IntAt β v a`: all coordinates of `a` in the basis `β` have `v`-valuation at most one.
- `BasisIntAt β v`: the structure constants (coordinates of `βᵢ βⱼ`) and the coordinates of
  `1` are `v`-integral.
- `intAt_add`, `intAt_neg`, `intAt_sub`, `intAt_smul` (by a `v`-integral scalar),
  `intAt_zero`, `intAt_basis`, `intAt_sum`, `intAt_one` and `intAt_mul` (the last two under
  `BasisIntAt β v`): integral elements form a `v`-integral order when the basis constants are
  integral. Products are expanded in coordinates with the structure constants and the
  ultrametric inequality.
- `exists_monic_of_intAt`: if `BasisIntAt β v` and `IntAt β v a`, then `a` is a root of a
  monic polynomial over `F` with `v`-integral coefficients, namely the characteristic
  polynomial of left multiplication by `a`: its matrix in `β` has `v`-integral entries, so
  its characteristic polynomial is the image of one over the valuation ring
  (`Matrix.charpoly_map`), and `a` is a root by the Cayley–Hamilton theorem
  (`LinearMap.aeval_self_charpoly`, applied to `1`).

## Provenance

Standard: the `𝓞_v`-span of a basis is an order at almost all places, and elements of an
order are integral. In the proof of Landherr's theorem this gives integrality of the global
element `y'` and its inverse outside a finite set of places, needed for the local
solvability of the norm equation there.
