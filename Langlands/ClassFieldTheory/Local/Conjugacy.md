# Conjugacy transport for relative Galois cohomology

This pair is authored by Worker 49. It constructs the actual
cohomology transport needed in Serre's conjugacy law for fundamental classes.
It makes no local class field theory claim.

Let `K -> L` and `K' -> L'` be field extensions, and let `eK : K ≃+* K'`
and `eL : L ≃+* L'` commute with their algebra maps.
`CompatibleFieldEquivalences` records exactly that square.
Its `symm` lemma proves compatibility of the inverse square.

`conjugateAutomorphism` sends `σ` to `eL ∘ σ ∘ eL⁻¹`.
Its certificate that the result fixes `K'` follows from the commuting square.
`galoisConjugacy` packages this map as a group isomorphism, with inverse the
conjugation by `eL⁻¹`. Both inverse identities and the multiplication law are
proved by evaluation.

`unitsConjugacy` transports actual units by the field isomorphism, uses additive
notation for the unit group, and restricts its integer-linear equivalence to
`IntegerScalars = ULift ℤ`. `unitsConjugacy_intertwines` proves compatibility
with the actual Galois actions.

`relativeConjugacy` then uses Mathlib's `groupCohomology.mapIso` on those
constructed maps. It is an isomorphism on actual relative group cohomology in
every natural degree. This is not an assumed cohomology equivalence or a
replacement group. No Galois, finiteness, local-field, or characteristic
assumption is needed for this transport itself.

The extension carriers `L` and `L'` share an arbitrary universe `u` because
Mathlib's cohomology isomorphism lives in one `ModuleCat (ULift.{u} ℤ)`.
The base carriers have independent arbitrary universes `v` and `w`.
No reduction to Type 0 is made.

Source: Jean-Pierre Serre, *Local Fields*, 1979,
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
Chapter XI, §1(iv), printed page 166 (PDF page 172), constructs the
operation by the inverse group conjugation and forward coefficient map.
Chapter XI, §2, Proposition 1(iii), printed page 167 (PDF page 173), and
§3, fundamental-class conjugacy formula, printed page 168 (PDF page 174).
Serre uses conjugation of fields inside a common closure. A commuting pair of
field isomorphisms is the intrinsic form of that operation, including a moving
base field. This file constructs only the transport; the invariant and
fundamental-class compatibility assertions belong in downstream proposition
families. It introduces no Frobenius convention itself.

Mathlib correspondence, pinned commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`Units.mapEquiv`, `AddEquiv.toIntLinearEquiv`,
`LinearEquiv.restrictScalars`, and `groupCohomology.mapIso`.
The latter constructs inverse maps on cohomology using its functoriality
certificates. The equivariance certificate supplied here is proved directly.

The imported project interface is the published
`Langlands.ClassFieldTheory.Local.Cohomology` module, authored by Worker 42.
It supplies `IntegerScalars`, `unitsRepresentation`, and
`relativeCohomology`. This module constructs the compatible field square and
its transport directly from that interface and the listed Mathlib operations.
