# Integral root points in a full-kernel centralizer component

This internal construction lifts an ambient integral root section into the
canonical integral dynamic unipotent of its full character-kernel centralizer
component. It retains arbitrary universe `u`.

Supply an integral model `M` over a domain `R` with supplied fraction field `K`,
an integral split torus map `i`, an integral character `a`, and actual
`KernelCentralizerData D` for its full scheme-theoretic kernel. The full
centralizer is smooth affine and closed in the ambient model. Its relative
identity component is smooth with geometrically connected fibres; its inclusion
in the full centralizer is open.

For an integral torus cocharacter `ν`, let `χC` be its composition with
`D.torus hT` and `χF` its further composition with `D.componentHom`.
`fullUnipotentToComponent` factors the canonical dynamic unipotent inclusion
for `χF` through the actual relative identity component. The dynamic subgroup
has geometrically connected fibres by `dynamicBaseSmoothConnected`, which
supplies this factorization. Its composition with the component inclusion
is the original full dynamic inclusion.

Assume `R` is a discrete valuation ring and `ν` pairs positively with `a`.
`exists_integralRootUnipotentLift` takes an ambient integral section `x` whose actual
generic restriction lies in the intrinsic root functor for the base-changed
torus map and character. It proves the existence of an integral section of the canonical
dynamic unipotent scheme for `χC`. Its image through that inclusion, the
relative component inclusion, and the full centralizer inclusion is exactly
the original integral section `x`. `integralRootUnipotentLift` chooses such
a section and retains this exact equation in its subtype.

The generic root comparison first gives a dynamic point in the component.
Its image in the full centralizer lies in the full dynamic unipotent.
That full dynamic subgroup and the full centralizer are both closed, so their
composite is closed in the ambient model. The integral closed-subgroup lifting
theorem lifts `x` into the full dynamic subgroup. The connected-fibre
factorization above sends this integral lift into the relative component.
Monicity of the actual inclusions identifies its generic restriction with the
original component dynamic point. Finally the closed canonical dynamic
unipotent inside the component lifts that section into its integral
coordinates. Affineness of the component model over a DVR supplies the
integral model used in this final closed-subgroup step.

The provenance is internal composition of the all-test generic root comparison,
dynamic functoriality, smooth connected dynamic representability, relative
identity-component factorization and integrality through actual closed
subgroups. The construction never assumes the component inclusion is closed.
It imposes no Henselian, residue-field, reductivity, nonidentity, or actual-root
hypothesis beyond the stated positive pairing and generic subgroup membership.
It supplies an integral root lift, not the reductive quotient, a nonzero
quotient reduction, or the host opposite-factor theorem.
