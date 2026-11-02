# The actual structure-map kernel as a module

The namespace `Langlands.AlgebraicGeometry.Picard.StructureKernelModule`
constructs a module structure on the actual additive kernel of the structure
map of any morphism `i : Y ⟶ X` of schemes at universe `u`. No closed
immersion or nilpotence hypothesis is needed for the construction.

For an open `U` of `X`, its sections are precisely

\[
\ker\bigl(\mathcal O_X(U)\longrightarrow
  \mathcal O_Y(i^{-1}U)\bigr).
\]

The scalar action is the usual multiplication by sections of
\(\mathcal O_X\). The restrictions
are the restrictions already defined in the published
`SquareZeroUnitKernels.additiveKernelPresheaf`. Ring-map multiplicativity
proves their semilinearity. `kernelModule` uses
`PresheafOfModules.ofPresheaf` to retain exactly that abelian presheaf and
the sheaf proof from `SquareZeroUnitSheaves`.
`kernelModuleUnderlyingIso` is the identity comparison between its
underlying abelian sheaf and the published `schemeAdditiveKernelSheaf i`.

The reused `Langlands.Scheme.Modules.unitToPushforwardUnit` is the actual map from `structureModule X` to the actual
module pushforward of `structureModule Y`. The published construction uses `i.c` by
forgetting rings to abelian groups and proving linearity for the scalar
restriction action. `structureMap_app` states that its value on every open
and every section is exactly `i.app U a`.

`kernelModuleι` is the actual ideal inclusion; `kernelModuleι_app` states
that it sends an ideal element to its underlying section. Its composite
with `unitToPushforwardUnit` is zero. Given any module morphism
`k : M ⟶ structureModule X` with zero composite, `kernelModuleLift`
restricts each component of `k` to the actual kernel ideal. The zero
composite proves membership, linearity comes from the component of `k`,
and naturality comes from the naturality of `k` after forgetting the
subtype. The lift composed with the inclusion is `k`. The inclusion is
injective on every open, so this factorization is unique. These arguments
construct `kernelModuleIsKernel`, the full categorical kernel universal
property. `kernelModuleIso` then compares this actual module with
`Limits.kernel (unitToPushforwardUnit i)` by uniqueness of limits.

If `i` is affine, `kernelModule_isQuasicoherent` proves that this actual
module is quasi-coherent. Both structure modules are quasi-coherent;
affine pushforward preserves quasi-coherence; and kernels of maps of
quasi-coherent modules are quasi-coherent. The proof uses the published
`Modules.CechDegreeOne.isQuasicoherent_unit` and
`Modules.QuasicoherentLocal.isQuasicoherent_pushforward` and
`isQuasicoherent_kernel`, then transports the property along
`kernelModuleIso`. In particular, the hypothesis applies to closed
immersions through the existing affine-morphism instance.

If `X` is locally noetherian, `kernelModule_hasFiniteAffineSections`
proves that the sections of the actual kernel are finite modules over
\(\mathcal O_X(U)\) for every affine open `U`. The structure module has finite affine sections
because each coordinate ring is a finite module over itself. The published
`Modules.HasFiniteAffineSections.kernel` passes this property to its
categorical kernel on a locally noetherian scheme, and `.of_iso`
transports it to the actual module. This finiteness conclusion imposes
no affine hypothesis on `i` and requires no quasi-coherence hypothesis.

This is an internal derived adapter. Its provenance is the published
actual additive-kernel construction, the actual scheme structure-module
and pushforward functors, the published module closure lemmas, and
Mathlib's module-presheaf constructor and categorical kernel uniqueness.
It identifies the actual additive sheaf with an actual module to which
existing coherence and finiteness results apply. Module cohomology versus
abelian-sheaf cohomology, H1/Picard classification, deformation
classification, and the final Picard representability theorem remain
separate obligations. The module imports no unpublished candidate.
