# M144.073: inverse corrections tend to the inverse minus one

Worker 643 adapts Naganori Yamaguchi's
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1381–1398,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original author/copyright header and Apache-2.0 LICENSE and NOTICE are
retained; the latter files are in `licenses/NYLL/`.

The public theorem proves the exact published U069 target with its original
field, Galois, valuation-extension, local-field, lattice-containment and
unit-membership hypotheses. It states convergence in `L` of the finite
inverse-correction sums to the image of the inverse valuation-ring unit minus one.

M144.072 supplies convergence of one plus those correction sums to the image of
the inverse unit. Subtracting the constant sequence one gives the required limit.
The simplification using `sub_eq_add_neg`, associativity and commutativity
cancels the added one at every index, leaving the correction sum itself.

Dependencies: the unchanged U069 statement module and the M144.072 proof module,
with its M144.071, M144.069 and M144.063 dependencies. The proof uses
`Tendsto.sub`, `tendsto_const_nhds` and additive simplification. Namespace/imports
and the explicit named target application are adapted; the source proof route is
retained. This is a limit in `L`. Membership of its limit in a closed lattice,
inverse closure of a principal-unit set and host reciprocity are subsequent
obligations, not conclusions of this theorem.
