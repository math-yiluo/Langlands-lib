# Finite fields of definition of specified group-scheme isomorphisms

This internal extension of `Descent.FiniteStageHom` retains an actual specified
isomorphism over an algebraic field extension in a finite model and supplies
the resulting all-test local group isomorphism. All fields and schemes have an
arbitrary common universe `u`. The source and target groups need not commute.

For any existing `HomModel k Ω f`, `HomModel.isIso` shows that invertibility of
`f` implies invertibility of the model's homomorphism. Its recovery equation
identifies the pullback of that homomorphism to `Ω` with `f` conjugated by the
two tower comparison isomorphisms. This composite is invertible. The extension
from the model's field of definition to `Ω` is faithfully flat and
quasi-compact, so the published `isIso_of_baseChange` reflects invertibility.
This argument applies to any model; it needs none of the algebraicity,
compactness or presentation assumptions used to construct one.
`HomModel.iso` is the associated actual finite-stage isomorphism, with forward
arrow exactly `D.hom`, as recorded by `HomModel.iso_hom`.

For `e : G_Ω ≅ H_Ω`, `IsoModel k Ω e` consists of a finite intermediate field
`E`, an actual isomorphism `G_E ≅ H_E`, and the exact recovery equation for its
forward arrow. `IsoModel.recovery_iso` expresses the same recovery as equality
of the composed actual isomorphisms. In particular, the package retains the
given `e`; it is stronger than existence of some isomorphism with the same
source and target.

When `Ω/k` is algebraic, `G` is quasi-compact and quasi-separated over `k`,
and `H` is locally of finite presentation over `k`, `nonempty_isoModel`
constructs this package. Apply the published homomorphism model theorem to
`e.hom`, then the preceding reflection argument supplies its inverse at the
same finite stage. `isoModel` chooses a package. No separate model for the
inverse and no enlargement of the finite intermediate field is required.

`IsoModel.localIso` applies the published actual-isomorphism-to-local-family
construction to the package's finite-stage isomorphism. Its multiplicative
equivalences range over every relative scheme-valued test, and are natural in
every test morphism. Finally,
`exists_finiteSeparable_localIso_of_separableClosure` specializes the
construction to `Ω = SeparableClosure k`. The resulting finite intermediate
field is separable over `k`, and its subtype carrier lies in `Type u`.
The theorem outputs its field and algebra structures, finite dimensionality,
separability, and a nonempty all-test `LocalGroupIso`.

The provenance is internal: this module uses the exact published finite
homomorphism model, fpqc reflection, tower comparison and local-family
interfaces. It assumes both ground-field groups and an actual isomorphism over
the extension. It supplies no quasi-split model, adjoint quotient, initial
separable-closure isomorphism, or inner-discrepancy equation; those remain
structural obligations of quasi-split inner-form existence.
