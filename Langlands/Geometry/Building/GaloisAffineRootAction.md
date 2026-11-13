# Actual coefficient transport of affine roots

`KPApartmentData.GaloisAffineRootStabilityStatement` and its proof
`KPApartmentData.galoisAffineRootStability` work over an arbitrary field extension
`K/k` in universe `u`. The supplied data are a commutative group scheme `T`, an
affine group scheme `G`, a map `i : T.toGrp ⟶ G` whose base change to `K` is
monomorphic, an arbitrary function `ω : Kˣ → ℝ`, a KP apartment for the
base-changed inclusion and `ω`, and stability of its full valuation class under
the existing coefficient action. For each `K/k` algebra automorphism, the
statement says that inverse precomposition by the actual coefficient affine
action carries the complete ordinary affine-root set onto itself. There is no
local-field or characteristic hypothesis.

Inverse precomposition transports affine functionals. The published covariance
of root forms identifies their derivatives. Exact filtration transport
identifies the images of affine root groups; adding a positive constant gives
the strict groups. Coefficient conjugation also carries each double-root group
onto the corresponding group, including the trivial-group convention when the
double is not a root. Thus the noncontainment condition defining an ordinary
affine root is preserved and reflected. The entire original affine-root set is
therefore carried onto itself.

The published inputs are `galoisAffineAction` from
`ApartmentGaloisAction`,
`rootForm_galoisTranslationAction`,
`rationalConjugate_mem_filtration_iff`,
`RelativeRoot.rationalConjugate_mem_subgroup_iff`,
`mem_roots_galois_iff` and the existing definitions in `KPApartment`.
The latter definitions retain the full noncontainment test
`U_ψ ⊈ U_ψ^+ · U_{2a}(K)`; the proof does not replace it by the simpler
nontrivial-jump test. The transport operation is
`AffineRootSystem.affineFunctionalTransport` from `AffineWeylTransport`.
All conclusions are deductions from these published definitions and theorems,
so the contribution has internal provenance.

This result does not construct a descended model, an invariant chamber or a
special apartment through a prescribed fixed point. In particular it does not
prove `UnramifiedFixedPointSplitTorusStatement`; its role is to establish the
root-arrangement covariance needed for actual facet transport.
