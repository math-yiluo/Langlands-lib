# The intrinsic field module of first-order line-bundle classes

This is an internal construction from the published
`Picard.DualNumberDeformationScaling`,
`Picard.DualNumberDeformationH1` and
`Modules.ProperCoherentCohomologyFiniteProof` results. No additional
source-specific theorem is assumed.

Let `k : Type u` be any field, let `X : Scheme.{u}`, and let
`f : X → Spec k`. As in the imported modules,
`preservation : pullbackTensorComparisonIsIsoStatement.{u}` is the
pullback/tensor comparison used to define the line-bundle class group.
The Library proves this proposition in `Modules.PullbackTensorProof`;
it is retained as an explicit parameter here to reuse the existing class
types.

`DeformationClasses preservation f` consists of actual line-bundle
isomorphism classes on the actual dual-number thickening of `X` whose
ordinary zero-section pullbacks have trivial isomorphism class. The type
retains no chosen trivialization. Its multiplication comes from the actual
sheaf tensor product; `Additive` writes that operation additively.

`deformationSMul` defines scalar multiplication directly: `c • q` is the
ordinary pullback of the class `q` along the actual thickening endomorphism
`scale f c` induced by `ε ↦ c ε`. The imported `scaleClass` already proves
that this pullback preserves the subgroup of deformations.
`smul_deformationClasses` records this defining formula, including `c = 0`.
The scalar operation requires no properness, separatedness or
quasi-compactness.

For separated `f` that is quasi-compact over `Spec k`, `deformationModule`
proves the field-module laws for this scalar operation and tensor addition.
It chooses the published finite ordered affine cover
`CechResolution.orderedAffineCoverOfQuasiCompact f`, then uses the
injectivity of `deformationH1AddEquiv`. The imported theorem
`deformationH1AddEquiv_scaleClass` says that the specified actual pullback
operation corresponds to multiplication by `c` on derived `H¹`.
`Function.Injective.module` therefore reflects the module laws from that
cohomology module. The cover is used to prove the laws; the scalar
operation itself was already defined without a cover.

`deformationH1LinearEquiv` upgrades the existing additive equivalence to
a `k`-linear equivalence with actual derived structure-sheaf `H¹` for
every ordered affine cover. Its scalar-compatibility field is the same
actual-pullback theorem. `deformationH1LinearEquiv_apply` states that its
underlying function is the existing additive comparison. The cocycle
formula states that the bundle with transition units `1 + ε z` goes to
the actual derived cohomology class `allPairsH1Map z`. The rank equality
is `LinearEquiv.finrank_eq`.

If `f` is proper, `finiteDimensional_deformationClasses` proves that this
intrinsic field module is finite dimensional. The published
`properCoherentCohomologyFinite` theorem applies over the noetherian field
`k` to the structure sheaf. The latter is quasi-coherent by the imported
`CechDegreeOne.isQuasicoherent_unit`, and its sections on any affine open
are a finite module over themselves. Thus its actual derived `H¹` is
finite, and the inverse of `deformationH1LinearEquiv` transfers that
finiteness to the deformation module. Properness supplies the
separatedness and quasi-compactness hypotheses used by the module
construction.

The scope includes empty and nonreduced proper schemes over arbitrary,
possibly imperfect fields, with no projectivity, smoothness, connectedness,
point or global-functions hypothesis. This result concerns ordinary
zero-section-trivial classes. It does not identify them with a pointed
deformation groupoid at every line bundle, construct infinitesimal
automorphisms, establish Rim-Schlessinger conditions, or construct a smooth
atlas. Those comparisons and constructions remain separate obligations.
