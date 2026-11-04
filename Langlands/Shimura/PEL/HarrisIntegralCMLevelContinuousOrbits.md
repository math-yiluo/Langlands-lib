# Finite continuous actual Harris monodromy orbits

This internal construction uses the same integral-action family, actual full
Weil frames, actual finite-etale fundamental group, and Tate and Tate-twist
monodromy prerequisites as `HarrisIntegralCMLevelContinuousMonodromy`.
It assumes nonemptiness of the unchanged raw integral-action tower at one
compact open level `U`.

For an invariant raw `U`-orbit represented by a frame `eta`, the preceding
continuity theorem makes the coordinate monodromy `rho(eta)` continuous.
At any other compact open level `V`, choose a frame representative of a raw
orbit class and write its coordinate as `g`. The already proved stabilizer
criterion identifies its stabilizer with the preimage of the open subgroup
`V` under the continuous map `gamma ↦ g⁻¹ * rho(eta)(gamma) * g`.
Thus every actual raw stabilizer at `V` is open. Nonemptiness at `U` supplies
the invariant orbit and its frame representative.

Equip the entire raw orbit set at `V` with the discrete topology. The open
stabilizer criterion for group actions proves that its actual monodromy
action is continuous. Each individual monodromy orbit is finite by
`HarrisIntegralCMLevelFiniteOrbits`. The principal definition bundles that
same orbit subtype with its actual restricted action as an object of
`ContAction FintypeCat Gamma`; the finite type is supplied by the established
finiteness, and its action is continuous because a subtype point has the
same stabilizer as its underlying raw class.

The provenance is internal and the proofs use the existing coordinate,
continuity, and finiteness results. No finiteness of the whole raw level set,
unconditional frame existence, representing scheme, normalized-isogeny
comparison, or completion of the host representability target is asserted.
