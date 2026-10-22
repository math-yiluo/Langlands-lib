# The underlying multiplicative Galois formation

This pair is authored by Worker 49. `FormationData A` packages the underlying
formation of Serre XI.1 for an actual representation `A`. It specifies a
family of finite-index subgroups, closed under finite intersections,
passage to an overgroup, and conjugation, with each module element fixed
by one member of the family. The empty intersection is recorded as
`top_mem`, and `inf_mem` handles binary intersections.

Serre states the module condition as membership of each stabilizer in
the subgroup family. The `locally_fixed` formulation here is equivalent:
a stabilizer contains the displayed fixing subgroup, and `upward_mem`
then puts the whole stabilizer in the family. Conversely a stabilizer
itself can serve as that subgroup. No cohomological vanishing, invariant
map, fundamental class, or reciprocity statement is a field of this
structure.

This entry module also imports the paired `Conjugacy` and
`FundamentalClasses` modules. Together they form one definition group:
the actual underlying multiplicative formation, its genuine relative
cohomology transport, and the normalization and functoriality predicates
for fundamental classes. None asserts local class field theory.

`multiplicativeFormation K` constructs these data for a perfect field
`K : Type u`. Its group is the actual
`Field.absoluteGaloisGroup K = Gal(AlgebraicClosure K / K)`;
its module is the actual additive notation for `(AlgebraicClosure K)ˣ`
with the usual Galois action and the explicit scalar ring `ULift.{u} ℤ`.
The admissible subgroups are exactly the subgroups open in the Krull
topology. The exact identification is exposed by
`mem_multiplicativeFormation_iff`.

The certificates reuse Mathlib: intersections of open sets are open,
an overgroup of an open subgroup is open, and conjugation is continuous.
The conjugation field is expressed as the preimage under `g(-)g⁻¹`,
which is the subgroup `g⁻¹ H g`; as `g` ranges over the group this is
exactly closure under all conjugates.
An open subgroup of this compact Galois group has a compact discrete
coset quotient, hence finite index. Finally, `unitOpenStabilizer` and
`mem_unitOpenStabilizer_iff` give an actual open fixing subgroup for
each closure unit.

`formationField K H` is the actual intermediate fixed field of an open
subgroup `H`. `fixingSubgroup_formationField` recovers `H`, by the existing
infinite Galois correspondence for the closed subgroup underlying `H`.
The `formationField_finiteDimensional` instance obtains its finite
extension certificate from `InfiniteGalois.isOpen_iff_finite`. Thus the
formation's field indexing uses genuine finite subfields of the closure.

The perfectness hypothesis makes the algebraic closure a separable
Galois closure, so Mathlib's compactness theorem applies directly.
It is not an additional restriction on the local-field theorem:
every finite extension of `ℚ_p` has characteristic zero and is perfect.
The carrier universe `u` is arbitrary; neither the field nor its
Galois group is replaced by a Type-0 model.

Source: Jean-Pierre Serre, *Local Fields* (1979),
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
Chapter XI, §1, printed pages 164--165 (PDF pages 170--171):
conditions (a)--(c), the Galois-field example, and condition (*)
on the module. For a profinite group, the open subgroups used here are
also closed and have finite index; conversely a closed finite-index
subgroup is open. Thus this construction realizes the same subgroup
family as that example.

Mathlib correspondence at commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`Field.absoluteGaloisGroup`, the `CompactSpace Gal(K/k)` instance in
`Mathlib.FieldTheory.Galois.Profinite`,
`Subgroup.isOpen_mono`, `IsTopologicalGroup.continuous_conj`,
and `Subgroup.finiteIndex_of_finite_quotient`.
The fixed-field declarations also reuse
`InfiniteGalois.fixingSubgroup_fixedField` and
`InfiniteGalois.isOpen_iff_finite`.
`Langlands.ClassFieldTheory.Local.unitOpenStabilizer` specializes Mathlib's open-stabilizer
theorem for integral field extensions to actual units.

The imported project interface is the published
`Langlands.ClassFieldTheory.Local.Cohomology` module, authored by Worker 42.
The accompanying `Conjugacy` and `FundamentalClasses` pairs are included in
this coherent definition group. The class-formation axioms in XI.2 remain
conclusions to be asserted in the downstream local realization proposition;
they are not certificates of this underlying formation.
