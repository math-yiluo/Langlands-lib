# Scalar sections of line bundles on quasi-compact quasi-separated schemes

This internal supporting construction defines
`CechResolution.scalarSectionsBaseChangeIso_lineBundle_qcqs`. For a line bundle
`L` on a compact, quasi-separated scheme `X`, a flat ring map `φ : R ⟶ S`,
and a pullback square over `Spec.map φ` whose projection `g : Y ⟶ X` is
affine, it identifies scalar extension of the actual relative global sections
of `L` with the actual relative global sections of its pullback. The
isomorphism's forward map is exactly the published
`DerivedSections.scalarSectionsBaseChangeMap`; the final simp lemma records
this equality. The construction preserves the published line bundles, tensor
products and sections maps.

The proof uses the degree-zero augmented Čech sequence of a finite
affine open cover. A nonempty finite intersection of cover opens is compact by
quasi-separatedness. It is separated because it is an open subscheme of its
first affine open. Thus the published separated line-bundle sections comparison
from `FieldGlobalFunctions` applies to each such intersection. The published
scalar factor comparison identifies these maps with the actual maps in the
Čech complex. The finite biproduct comparison consequently makes the scalar
Čech sections map invertible in degrees zero and one (indeed in every degree).

Applying relative sections to the augmented sequence preserves its kernel
because relative sections is a right adjoint. Flat scalar extension also
preserves that kernel. The augmentation square commutes for the canonical
scalar sections map: equality on the tensor generators `1 ⊗ m` reduces to
the published sheaf augmentation square. A short-complex argument then shows
that this canonical map is invertible. It constructs an inverse by lifting
the target augmentation followed by the inverse degree-zero comparison
through the source kernel; monicity of both augmentations verifies both
inverse equations.

All mathematics here is derived internally from Mathlib's quasi-separatedness,
separated open subschemes and exact short-complex APIs and the Library's
published Čech, scalar factor and separated line-bundle base-change
constructions, imported by their Lean names. This is a sections construction;
it supplies neither a higher-cohomology comparison for nonseparated schemes
nor the final reflection-of-ampleness theorem.
