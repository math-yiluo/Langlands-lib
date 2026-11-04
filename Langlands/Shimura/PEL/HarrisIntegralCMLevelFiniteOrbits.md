# Finite actual monodromy orbits from an invariant Harris level

This internal construction keeps the actual direct pulled integral-action family,
its pulled dual witness and polarization map, its full Weil frame type, and the
actual Tate and Tate-twist monodromy actions of
`HarrisIntegralCMLevelMonodromy`. All torsion and geometric-point prerequisites
are retained. The arithmetic carriers and schemes are in universe zero.

The private helper `compactOpen_cosetImage_finite` uses the existing topology of
a topological group. For compact open subgroups `U` and `V` and an element `g`,
the map `u` to the left coset of `u * g` in `G / V` is continuous. Its image of
`U` is compact. The quotient is discrete because `V` is open, so that image is
finite. No normality is required.

`harrisIntegralCMFrameOrbit_finite_of_fixed` assumes a chosen actual frame `eta`
whose raw orbit at an original compact open level `U` is monodromy invariant.
The existing base-fixed criterion places every actual coordinate `rho(gamma)`
in `U`. For an arbitrary raw orbit at a level `V`, choose a frame representative
and its coordinate `g`. By actual equivariance and the original-group coset
equivalence, the monodromy orbit lies in the image of the finite set of cosets
of `u * g` with `u` in `U`. Hence that individual raw monodromy orbit is finite.

`harrisIntegralCMFrameOrbit_finite_of_level_nonempty` instead assumes nonemptiness
of the existing, unchanged `harrisIntegralCMFullActionLevelTower` at `U`. It
chooses a representative of that invariant raw orbit and applies the preceding
result. It does not assume frame existence separately and proves finiteness of
every individual monodromy orbit at every level `V`.

`harrisIntegralCMFrameMonodromyOrbitFinset` enumerates that actual finite orbit.
Its membership theorem characterizes an element as a monodromy translate of the
original class. The enumeration uses the finite-set construction and is
noncomputable; its value is precisely the orbit, independent of the choices in
the finiteness proof.

The provenance is internal: the proof combines the previously constructed
actual Harris monodromy coordinates and coset equivalence with Mathlib's
quotient topology and compact discrete finiteness theorem. No further original
literature assertion is made. This result is conditional on a nonempty raw
level and does not assert that the whole frame-orbit set is finite. It supplies
no continuity of the monodromy coordinate map or action, no open stabilizers,
no finite-etale representing scheme, and no comparison with normalized
rational-isogeny moduli classes. The host representability target remains open.
