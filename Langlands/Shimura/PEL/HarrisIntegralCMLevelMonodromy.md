# Original Harris coordinates for actual integral-family monodromy

This internal construction fixes the actual universe-zero Harris arithmetic
data, a polarized-family dual witness and map, a direct pullback of that family,
and an actual action of the specified Harris integral order. It uses the existing
named prerequisites for Weil frames, torsion and geometric monodromy.
The algebraic construction does not require the full determinant condition or
an assumed faithful action: an actual frame is supplied where coordinates are
needed. The test scheme is quasi-separated. Geometric monodromy uses the supplied
finite-fibre condition, torsion theorem, and invertibility, finiteness and etaleness
conditions for the roots-of-unity systems. No existence of a frame is concluded
without the stated input.

`harrisIntegralCMWeilFrame` is the existing full Weil frame type for precisely
that direct pulled family, its pulled polarization map and its rationalized
integral action. Write `G` for the original opposite Harris finite-adelic group
and `H` for the scalar-extension similitude group of the Harris Hodge form.
`harrisIntegralCMFrameEquiv` composes the published continuous group equivalence
from `G` to `H`, used here only algebraically, with
`weilAdelicFrameSourceEquiv` at a chosen actual frame `eta`. The regular Harris
source satisfies rational PEL conditions by `hodgeRationalPELConditions`, and
simplicity supplies the required nontriviality. Evaluation at a group element
is actual right precomposition. The identity coordinate is `eta`; multiplication
corresponds to successive right precomposition. These are the `apply`, `one` and
`mul` theorems.

For an original compact open level `U`, the scalar subgroup is exactly
`((hodgeLevelFunctor D C).obj U).subgroup`.
`harrisIntegralCMFrameOrbit_eq_iff` proves that the actual raw frame orbits of
coordinates `g` and `k` are equal if and only if `g⁻¹ * k` belongs to
`U.subgroup`. In the forward direction an actual scalar-subgroup translating
element has a unique original-group preimage; the existing membership comparison
places this preimage in `U`. Coordinate injectivity then identifies `k` with
`g` times that preimage. Conversely the scalar image of `g⁻¹ * k` supplies the
actual right translation. `harrisIntegralCMFrameCosetEquiv` descends the coordinate
equivalence through precisely this relation to identify the left coset set
`G / U` with the actual raw right frame-orbit set. Normality of `U` is not needed.
Its `mk` theorem gives the representative formula. This is before monodromy
invariance and before the rational-isogeny class quotient.

`harrisIntegralCMFrameMonodromy` is the coordinate of the actual left geometric
monodromy translate of `eta`. The left action is the published
`weilAdelicFrameMonodromyAction` with `rationalWeilGeometricTransport`, including
Tate-twist transport. Its homomorphism laws follow by applying the coordinate
equivalence, using the right multiplication law and commutation of the actual
left and right actions. `harrisIntegralCMFrameEquiv_monodromy` identifies the
translate of the frame with coordinate `g` as the frame with coordinate
`rho(gamma) * g`. The coset representative version is
`harrisIntegralCMFrameCosetEquiv_monodromy_mk`.

`harrisIntegralCMFrameOrbit_stabilizer_iff` consequently says that `gamma` fixes
the raw orbit with coordinate `g` if and only if
`g⁻¹ * rho(gamma) * g` belongs to the original subgroup `U.subgroup`. It applies
the frame equivariance formula and the proved orbit-equality criterion, with
symmetry of orbit equality and associativity. The `fixed_iff` theorem quantifies
this equivalence over all monodromy elements. At `eta` itself,
`harrisIntegralCMFrameOrbit_base_fixed_iff` reduces the condition to all
`rho(gamma)` belonging to `U.subgroup`.

`harrisIntegralCMFullActionLevel_nonempty_iff` applies this to the unchanged
`harrisIntegralCMFullActionLevelTower`: given `eta`, its value at `U` is nonempty
if and only if there exists `g` for which every
`g⁻¹ * rho(gamma) * g` belongs to `U.subgroup`. For an existing invariant orbit,
the proof chooses a frame representative, takes its coordinate, and uses the
`fixed_iff` theorem. Conversely that theorem constructs the actual invariant
raw orbit from the supplied coordinate. The result retains the same family,
action, polarization map, point and original level subgroup.

The provenance is internal: the construction combines the existing Harris
scalar-extension group equivalence, actual source-frame equivalence, actual
commuting monodromy action, subgroup membership comparison, and Mathlib's
ordinary coset quotient. The proofs above describe these implemented algebraic
constructions; no additional assertion from the original literature is claimed.
This is a prerequisite for actual level geometry. No continuity of the
monodromy coordinate map, open stabilizers, finiteness, representing scheme,
normalized moduli representability, or equality with normalized isogeny classes
is asserted here.
