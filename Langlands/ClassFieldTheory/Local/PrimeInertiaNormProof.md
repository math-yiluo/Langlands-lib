# Prime-degree norm surjectivity over the actual inertia fixed field

This module proves `Langlands.LocalClassField.primeNormOverInertiaFixedField`
with exactly the published proposition
`Langlands.LocalClassField.PrimeNormOverInertiaFixedField.{u}` as its type.
For an arbitrary p-adic field `F` and a totally ramified finite Galois
intermediate field `D` of prime degree, put
`U := IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)`
and `V := U ⊔ D.field`. The theorem proves surjectivity of `normUnits U V`
for the literal inclusion algebra on `V`. It retains arbitrary universe `u`
and all field units, including elements of nonzero valuation, with no
additional outer hypotheses.

The private assembly `primeNormOverInertiaFixedField_of_bounded` takes
`PrimeNormAfterUnramifiedBaseChange` as a parameter. The public theorem
supplies the published proof
`Langlands.LocalClassField.primeNormAfterUnramifiedBaseChange`, imported from
`Langlands.ClassFieldTheory.Local.PrimeNormBaseChangeProof`.
The forward-disjointness input is discharged by the published theorem
`Langlands.PadicField.totallyRamifiedInertiaDisjoint`, imported from
`Langlands.Galois.Local.TotalRamifiedInertiaDisjointProof`. It proves that a
finite totally ramified Galois extension is linearly disjoint from the actual
canonical inertia fixed field, without a prime-degree restriction. The
finite-compositum input is discharged by the published theorem
`Langlands.LocalClassField.totalUnramifiedCompositum`, imported from
`Langlands.ClassFieldTheory.Local.TotalUnramifiedCompositumProof`.

For an arbitrary unit of the actual inertia fixed field, the implementation uses
the published `Langlands.PadicField.inertiaFixedFieldUnramifiedExhaustion` on its
singleton to obtain a finite unramified Galois stage and a unit at that stage.
The containment part supplies the literal inclusion of the stage. This applies
to the full multiplicative group, with no valuation-zero restriction.

The published finite-compositum theorem supplies the compositum with the original
prime-degree totally ramified field. Extending scalars and mapping through the
inverse of `Langlands.Weil.Local.intermediateClosureEquiv` realizes it as an
actual finite intermediate field in the stage's algebraic closure. Dimension,
Galois structure and absolute ramification index are transported to this model.
For the last invariant, an internal helper uses the published relation between
absolute ramification indices, extension degree and residue degree in both
directions: an algebra equivalence has degree one, so the indices divide each
other. Explicit `asPadicField` scalar and module instances keep these maps
compatible with the packaged fields.

The private `base_units_are_norm` helper applies the finite bounded norm
input to a base-field unit. It identifies the resulting finite compositum
with the finite prime model, then applies the published forward-disjointness theorem
over the new unramified stage. The published
`Langlands.PadicField.inertiaFixedFieldBaseChange` identifies the transported
inertia field with the actual inertia field there. The internal
`linearDisjoint_of_map` reflects disjointness through the compatible closure
embedding, using the injectivity of the induced tensor map and the commuting
square of multiplication maps.

The norm comparison `norm_sup_of_disjoint` restricts the two fields to their
literal compositum, reflects disjointness there, and applies Mathlib's
`Subalgebra.LinearDisjoint.norm_algebraMap`. Only the right field is assumed
finite dimensional. Its `norm_sup_over_subfield` adapter transports this identity
back from the presentation over the finite stage. Thus the finite norm witness
maps to a witness over the full inertia field. The redundant unramified stage
in the compositum is removed because it lies in the inertia field.

Finally the assembly applies this base-unit helper over the arbitrary finite
stage containing the original unit. `norm_preimage_of_equiv` uses Mathlib's
`Algebra.norm_eq_of_equiv_equiv` for an explicit commuting square.
`norm_preimage_of_map` specializes it to intermediate-field images, and
`norm_preimage_from_stage` returns from extended scalars to the original literal
compositum by restriction of scalars. `norm_preimage_of_eq` handles equal field
presentations by equality elimination. The original stage-unit inclusion equation
then gives the required original unit. Supplying the published bounded norm
proof completes the passage for arbitrary units at every universe level.

The route follows Serre, *Local Fields* (1979), Chapter V section 4, Proposition 6
and its corollary, printed pages 88–89 / PDF pages 95–96, with the setup on printed
page 87 / PDF page 94, registered source `serre-1979-local-fields`. The use of the
actual canonical inertia field and the closure-equivalence adapters is derived
formalization content, not a verbatim standalone theorem of the source.
Bounded norm solvability is supplied by its imported proof module.

Authored by Worker 366. The explicit transport of finite dimensionality through
`IntermediateField.equivMap` follows the implementation pattern in Worker 60's
shared `NormFieldModelsCheck` draft. Worker 60 is a contributing author of that
reused pattern. The generic norm APIs were identified in the coordination with
Worker 10; no unpublished proof term from Worker 10 is used here.

The imported finite-compositum proof was authored by Worker 159 with Worker 27
credited for its arithmetic route. It is used through its published theorem;
no source proof terms from that module are copied here.

The imported forward-disjointness proof was authored by Worker 104 with
Worker 366 credited for the finite-stage route specification. It is used through
its published theorem; its finite-support proof is not copied here.

The imported bounded norm proof was authored by Worker 27. This module uses its
published theorem and copies no proof terms from that module.
