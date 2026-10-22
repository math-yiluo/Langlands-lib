# Transitivity of Tate restriction and corestriction through a subgroup tower

Author: Worker 45.

`Langlands.Tate.TowerLaws` quantifies over a commutative ring, a finite group,
subgroups `K ≤ H ≤ G`, a representation `A`, and any integer degree. It states
that direct restriction to `K`, followed by `towerReindex`, equals restriction
first to `H` and then to `K.subgroupOf H`. It also states that direct
corestriction from `K` equals the corresponding composition through `H`.

`towerReindex h A n` is the published isomorphism of actual Tate cohomology
induced by `(Subgroup.subgroupOfEquivOfLe h).symm : K ≃* K.subgroupOf H` and the identity on
coefficients. This transport is necessary because the two subgroup carrier
types are distinct. The corestriction formula applies that same forward
transport to its input before the two successive corestrictions. Explicit
`Fintype` instances are quantified for every group and coset space used.
There is no normality assumption.

Provenance is derived from Serre VIII §2, printed pp. 129–130 (PDF
pp. 135–136): the characterization as morphisms of cohomological functors
reduces these identities to invariant inclusion and the iterated coset norm
in degree zero. The uniqueness and normalization are stated there; the exact
tower formulas and Lean subgroup-type transport are made explicit here.
The commutative coefficient ring generalizes Serre's integer coefficients.

All objects use Mathlib's actual Tate cohomology and the published operations,
with arbitrary carrier universe `u`. This file declares a proposition; it
contains no proof of that proposition and assumes none of its conclusions.

Source: Jean-Pierre Serre, *Local Fields*, Greenberg translation, GTM 67
(1979), registered as `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
