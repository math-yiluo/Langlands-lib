# M144.072: finite inverse approximations tend to the inverse

Worker 643 adapts Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1346–1380,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original author/copyright header and Apache-2.0 LICENSE and NOTICE are
retained; the latter files are in `licenses/NYLL/`.

The public theorem proves the exact published U069 target with its original
field, Galois, valuation-extension, local-field, lattice-containment and
unit-membership hypotheses. It states convergence in `L` of one plus each finite
inverse-correction sum to the image of the inverse valuation-ring unit.

M144.071 supplies convergence of the products of the unit with those
approximations to one. Multiplication of this limit by the constant image of the
inverse unit gives a new sequence with the desired limit. For every index,
`Units.inv_mul`, transported through `algebraMap 𝒪[L] L`, identifies the inverse
unit times the unit with one. Reassociating and cancelling identifies the new
sequence with the approximations in the target. `Tendsto.congr'` transfers the
limit along this equality at every index.

Dependencies: the unchanged U069 statement module and the M144.071 proof module,
with its M144.069 and M144.063 dependencies. The proof uses multiplication of
limits, `Units.inv_mul`, `congrArg` and eventual equality. Namespace/imports and
the explicit named target application are adapted; the source proof route is
retained. This result proves only the stated convergence in `L` and does not
assert membership of the inverse in a lattice or principal-unit set.
