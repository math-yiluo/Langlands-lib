# The unique place of an intermediate field above a place of Harris's data

Let `E ⊆ E' ⊆ L` be number fields, with algebra structures and the scalar tower
`E → E' → L`, and let `v` be a finite place of `E`.

* `finitePlacesAbove_subsingleton v h`: if `L` has exactly one place above `v`
  (`HasUniquePlaceAbove L v`, the hypothesis of Harris 1998, Section 4, on the
  places `v₁, c(v₁), v(*)₁, c(v(*)₁)`), then `E'` has at most one place above
  `v`, i.e. the type `FinitePlacesAbove E' v` is a subsingleton.

  Proof: for places `u, u'` of `E'` above `v`, choose places `w, w'` of `L`
  above them (every finite place has a place above it, Library
  `AdelicFunctoriality.exists_place_above`). By transitivity of lying over, `w`
  and `w'` lie above `v`, so `w = w'` by hypothesis. A prime of `E'` below a prime
  `w` of `L` equals the contraction of `w` (`Ideal.LiesOver.over`), so both `u`
  and `u'` equal the contraction of `w` to `𝓞 E'`.

* `PlaceDatum.uniquePlaceAbove P h`: for a place datum `P` of Harris's setup
  (places `P.v` of `E`, `P.v'` of `E'` above it, `P.vTilde` of `L`) with a unique
  place of `L` above `P.v`, the `Unique` structure on `FinitePlacesAbove E' P.v`
  whose default element is `P.v'`; `PlaceDatum.uniquePlaceAbove_default` records
  this.

Provenance: elementary consequence of the definitions used in the proof of
`HenniartGlobalizationStatement`. The Library's local restriction formula for
induced representations of relative Weil groups is a sum over the places of `E'`
above the base place; at Harris's place `v₁` this sum has the single term `P.v'`.
