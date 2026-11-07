# Coherence equations for actual scalar extensions of complete pinnings

For fields `k`, `K`, and `L` in an arbitrary common universe, assume a scalar
tower `k → K → L`, algebraicity of its three field extensions, an actual affine
`k`-group scheme `G`, and a supplied complete split pinning `p` of `G`.
`SplitPinning.baseChangeTowerTorusIso` is the canonical isomorphism between the
torus of the iterated scalar extension of `p` and the torus of its direct scalar
extension to `L`. `baseChangeTowerGroupIso` gives the corresponding actual
ambient group-scheme comparison, and `baseChangeTowerIndexEquiv` keeps the
supplied root indices unchanged.

The five `baseChangeTowerIso_*` theorems check all compatibility equations for
these specified comparisons: the torus-inclusion square, each root in the full
integral character lattice, each coroot in the full cocharacter lattice,
membership in the simple-root support, and the differential's value on each
chosen actual simple-root Lie vector. The support theorem is named
`baseChangeTowerIso_simple_iff`; the vector theorem is
`baseChangeTowerIso_rootVector`. The declarations with `Iso` in these theorem
names express equations for the comparison maps; this module does not package
them as a complete `SplitPinning.Iso`.

## Scheme and lattice comparisons

The preliminary `Descent` constructions apply to arbitrary scheme maps
`U → T → S` and `U → S` with a specified equality of composites.
`pullbackTestComparison` has identity underlying scheme map. The point formula
`pullbackComparison_points` follows by projection to the original group scheme.
The two canonical multiplicative-group comparisons preserve the same global
unit, so they agree on every relative scheme test. Forgetting or restoring
additive notation supplies the commutative-group version and its inverse
formula. Naturality then proves `characterBaseChange_tower`, its inverse
form, and `cocharacterBaseChange_tower`. These formulas compare the entire
integral lattices; no central directions are removed.

## Actual dual-number points and Lie vectors

For a tower of commutative rings, `Lie.algebraBaseMap_tower` expresses the
composition law on coefficient spectra. The dual-number coefficient maps
compose on their constant and infinitesimal components by the same scalar-tower
identity. `kernelFieldExtension_val_fst_eq` identifies the projection of an
extended actual Lie-kernel point with its original point preceded by this
coefficient-spectrum map. Applying that formula twice and projecting the
actual pullback comparison proves `kernelFieldExtension_tower_projection`.
Injectivity of the published kernel base-change equivalence then proves
`kernelFieldExtension_tower`, an equality of actual multiplicative
identity-kernel points.

For fields, the published formula for `schemeScalarExtension` on `1 ⊗ x`
identifies the successive linear scalar extensions with those same kernel
points. Additive notation and `targetMapLinear_ofMul` therefore yield
`schemeScalarExtension_tower_one_tmul`. The affine and finite-type hypotheses
needed by these linear constructions are stated in their sections; the
complete pinning supplies smoothness when its chosen vectors are used.

## Pinning equations

`baseChange_rootVector_kernel` converts the published root-vector base-change
formula to actual multiplicative kernel points. Its iterated version, combined
with the Lie-kernel tower identity, proves the tower vector equality first on
simple indices inherited from `p`. The equivalences of simple supports extend
it to every simple index of the iterated pinning. The generic
`rootVector_map_of_kernel` converts this equality to the canonical differential
equation. `rootVector_map_congr` transports it along proved equalities of the
ambient morphism and target simple index, giving the final named-map version.

The torus-inclusion square is the naturality equation of the actual pullback
comparison. The root and coroot equations specialize the lattice formulas
above, and the simple-support equivalence uses the support specification of
`SplitPinning.baseChangeBase`. The generic constructor `SplitPinning.Iso.ofKernel`
is also provided: for any two supplied pinnings over one field, it constructs
a pinned isomorphism from its actual torus and group isomorphisms, the lattice
and support equations, and the multiplicative kernel vector equation. Its
proof converts the last equation by injectivity of additive-to-multiplicative
notation.

## Provenance and scope

These are internal consequences of the published scheme pullback comparisons,
actual coefficient maps, and scalar transport of supplied pinnings, imported
from `Descent.Data`, `Lie.FieldExtension`, and `Reductive.PinnedScalarTransport`.
No external structural theorem is introduced. Algebraicity is required for the
pinning scalar extensions. This unit supplies comparison maps and their
compatibility equations, with a complete pinning still an input. Pinning
existence, a packaged pinned tower isomorphism, coherent semilinear descent,
and quasi-split inner-form existence remain separate obligations.
