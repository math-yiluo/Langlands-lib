# The inertia fixed field has the full supplied residue field

Worker 94 proves
`Langlands.LocalClassField.NYLL.FiniteInertiaResidueMapBijectiveStatement`
by the theorem `finiteInertiaResidueMapBijective` in the same namespace.
Worker 93 authored the imported supplied/spectral comparison used in the proof.
The base and extension universes `u` and `v` are independent. All three supplied
realizations `TF`, `TU`, and `TE` remain arbitrary.

This is a derived proof of the already published target in
`Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement`; its mathematical
provenance is the inertia fixed-field assertion described in that target's
paired Markdown, corresponding to Serre, *Local Fields*, III.5. The present
proof follows the residue-action Galois correspondence rather than a calculation
of ramification indices or residue degrees.

First, `spectralInertiaResidueInclusion_bijective` works with a complete
ultrametric norm on a field `K`, a finite Galois extension `L`, and the actual
intermediate field `U = fixedField (LocalGalois.inertia K L)`. It assumes finite
base and intermediate residue fields. The existing theorem
`LocalGalois.map_residueHom_fixingSubgroup` identifies the fixing subgroup of
`residueInclusion K L U`'s image field with the image of `U.fixingSubgroup` under
the spectral residue action. The finite Galois correspondence identifies
`U.fixingSubgroup` with inertia. Inertia is the kernel of that residue action,
so its image is the trivial subgroup. The residue extension is Galois because
its base field is finite and it is algebraic. The Galois correspondence for
this residue extension then makes the image field the whole residue field.
Thus the actual spectral residue inclusion is surjective; it is injective as a
homomorphism of fields.

For the supplied-data target, the proof installs the norm constructed from
`TF` exactly as in `finiteInertiaSubgroup`. The actual fixed field in the target
is therefore the same `U` used in the spectral argument. The imported
`suppliedSpectralIntegerEquiv` and `suppliedSpectralResidueEquiv`, applied to
`U` and `E`, identify their spectral rings and residue quotients with the
arbitrary supplied ones. Their integer-ring identifications preserve the
underlying field elements: both integer subrings are the integral closure of
the supplied base integer ring. The finite supplied residue field of `U`
therefore provides the finiteness needed in the spectral argument.

The local equality `hcomm` checks on integer representatives that the specific
map `finiteInertiaResidueMap F E TF TU TE` commutes with these residue
identifications and `LocalGalois.residueInclusion`. This square holds because
both integer maps are the actual inclusion `U → E`, and the comparison
equivalences preserve field elements. Spectral surjectivity, followed by the
residue equivalences and this square, gives a preimage of every supplied
residue element of `E`. Injectivity again follows from the field homomorphism.

No canonical realization replaces a supplied one. No residue equivalence,
valuation compatibility, or ramification property is assumed as an additional
premise. The target's Lean/Markdown pair and all its imported files are
unchanged. The proof constructs no reciprocity map and uses no Frobenius
normalization.
