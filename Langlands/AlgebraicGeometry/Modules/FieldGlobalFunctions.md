# Canonical global-functions base change over a field

This internal construction extracts ordinary sections from the published
canonical cohomology comparison. For a proper scheme over an arbitrary field,
it constructs the canonical scalar-extension isomorphism on global functions
for every affine change of base. The target ring may be nonreduced and need
not be noetherian. Nothing assumes that the field maps isomorphically onto
the global functions.

First, `CechResolution.lineBundleSectionsScalarBaseChangeIso` treats an
actual line bundle on any quasi-compact scheme separated over an affine
base. Its hypotheses are a Cartesian square of affine bases and a flat
ring map. The forward map is exactly the published
`DerivedSections.scalarSectionsBaseChangeMap`. The proof uses
`isIso_scalarBaseChangeMap_lineBundle` in degree zero and the identity
`scalarBaseChangeMap_zero`. The two zeroth-derived comparison maps are
isomorphisms, so cancellation proves invertibility of the ordinary
sections map. No higher-direct-image or Cech acyclicity assumption is
left to the caller.

`FieldGlobalFunctions.sections f` is the actual global sections of the
structure sheaf as a module over the given field, with scalar action
induced by the actual structure morphism `f`. The lemma `flat` records
Mathlib's flatness instance for a map to a field spectrum. For a proper
`f`, the lemma `finite` specializes
`properCoherentCohomologyFinite` to the actual structure sheaf and degree
zero. The trivial line bundle supplies quasi-coherence, and the sections
on every affine open are the coordinate ring, finite as a module over
itself. `relativeCohomologyZeroIso` transports finite generation to
ordinary global sections.

The selected construction `FieldGlobalFunctions.baseChangeIso` has source
`S ⊗_k Γ(X, O_X)` in the precise `ModuleCat.extendScalars` convention and
target the actual `S`-module `Γ(Y, O_Y)`, for every Cartesian square
`Y -> X` over `Spec S -> Spec k`. Properness supplies a finite ordered
affine cover of `X` and separatedness. The scheme map `Y -> X` is affine
because it is a base change of a map of affine schemes. Every ring map
out of the field is flat, including one to the zero ring. Apply the
ordinary-sections construction to the trivial line bundle, then apply
relative sections to the canonical `pullbackUnitIso`.
`baseChangeIso_hom` identifies its forward map as the actual scalar
sections map followed by this canonical structure-sheaf identification.
The construction therefore specifies the comparison map, not just an
abstract module isomorphism.

The provenance is internal assembly of the unchanged published
`CechResolution.LineBundleBaseChange`, `CohomologyBaseChangeZero`,
`ProperCoherentCohomologyFiniteProof`, and `PullbackUnit` modules, together
with Mathlib's field-flatness results. The construction supplies the
affine degree-zero module base-change and finiteness ingredients relevant
to cohomological flatness in the Picard argument. It does not construct
an algebra isomorphism, a global direct-image base-change isomorphism
on arbitrary bases, an automorphism group scheme, a comparison of etale
and fppf sheafifications, or Picard representability.
