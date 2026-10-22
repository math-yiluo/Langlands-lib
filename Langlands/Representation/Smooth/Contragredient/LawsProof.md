# Smooth contragredient laws: implemented proof

`Langlands.smoothContragredientLaws` proves the entire accepted proposition
[`Langlands.SmoothContragredientLawsStatement`](LawsStatement.md). All eight
component lemmas belong to this proof module.

The coefficient ring `R`, group `G`, and modules `V`, `W`, and `U` have five
independent universes. Coefficients are an arbitrary commutative ring; each
module is an additive commutative group with an `R`-module structure. Only the
group carries a topology. The closing theorem uses `omit [IsTopologicalGroup G]`
and then introduces that instance at the target's internal binder. Thus it
does not strengthen the accepted target by moving this hypothesis outside the
proposition.

The first six clauses require no smoothness of the original representations.
The seventh explicitly requires `IsSmooth rho`, and naturality requires
smoothness of both original representations. Admissibility, freeness, finite
dimension, compactness, and any topology on the modules or coefficients are
absent. The smooth dual is the smooth-vector submodule of the full algebraic
dual. The bidual map here is evaluation; these laws assert neither its
injectivity nor its surjectivity.

| Clause | Component lemma in namespace `Langlands` | Implemented argument |
| --- | --- | --- |
| Smoothness | `isSmooth_smoothContragredient` | Retain the open subgroup in the smooth functional's membership witness. Its equation in the full dual yields the equation in the restricted action by `Subtype.ext`. |
| Inverse-action evaluation | `smoothDualPairing_action` | Definitional equality: evaluating `g` acting on a functional at `v` evaluates the original functional at `rho(g inverse)v`. |
| Invariant pairing | `smoothDualPairing_invariant` | Rewrite by the preceding formula and `rho.inv_self_apply`. |
| Pullback evaluation | `contragredientMap_apply` | Definitional equality: pullback along `f` evaluates at `v` as the original functional at `f(v)`. |
| Identity | `contragredientMap_id` | Extensionality in a smooth functional and a vector reduces the map equality to `rfl`. |
| Reversed composition | `contragredientMap_comp` | The same extensionality proves `contragredientMap (g.comp f) = (contragredientMap f).comp (contragredientMap g)`. |
| Smooth bidual evaluation | `smoothBidual_apply` | Definitional equality: the canonical image of `v` evaluates a smooth functional at `v`. |
| Bidual naturality | `smoothBidual_natural` | Extensionality in `v` and a smooth functional on the target makes both composites evaluate that functional at `f(v)`. |

The closing proof introduces the topological-group instance and assembles these
eight lemmas in the order of the accepted conjunction. Its only project import
is the target module. The complete import closure consists of the four
construction pairs below and Mathlib; no separate project law proof is used.

## Exact target and dependencies

The target is artifact `ff1e06de-a5b0-4bc7-81b5-8b4555029cef`, version 1,
with target fingerprint
`7a4c05be19458544adc2e58b201936bf9d24bff54fcd858b8582dc4680ad951e`.
Its publication commit is `9db46907db3181b0c1dfd287b8ab2f1f02054cab`;
its independent semantic receipt is `8b4e2509fa1640b0a6198dfe571d334d`.

The exact definition dependencies are:

| Construction | Accepted artifact | Version |
| --- | --- | --- |
| Smooth contragredient and smooth bidual map | `be3f8221-aa6f-4069-8faa-f04e1f5dc4b7` | 1 |
| Algebraic dual maps | `079d7c1a-8b96-4917-997a-536d6954d55b` | 1 |
| Smooth part | `9fb5627f-6e8c-48a5-a92f-a4ddcf319b2d` | 1 |
| Smoothness and fixed vectors | `665022df-625b-44ae-9dbd-425f6e266bab` | 1 |

The prepared environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`,
version 1: Lean 4.34.0, commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The target and all four definition
artifacts are accepted, published, and currently available at the checked
Library commit `5bc58c2525e0499012801c80f17b6a9c04d57263`.

## Provenance and validation boundary

The source context inherited from the accepted target is Casselman,
*Introduction to admissible representations of p-adic groups*, Chapter II,
revision June 16, 2019, Section 3, page 6: the opening paragraphs for the
inverse-action dual, smooth contragredient, and invariant pairing, and the
paragraph after Corollary II.3.3 for reversal of equivariant maps.
The registered original is `casselman-2019-smooth-representations`, SHA256
`2f7868c9e29fd486a42419f5b381237bba5d0ba73accc82ed5d7ade448a79c3d`,
retained at
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter II - Smooth representations--2019.pdf`.

The implemented proofs are direct internal consequences of the accepted
constructions. In particular, bidual evaluation and naturality do not use
Lemma II.3.2's stronger isomorphism assertion or Corollary II.3.3's exactness
conclusion. The direct arguments above justify the accepted broader ring and
group hypotheses.

Worker 0 authored the complete Lean proof and its initial explanation.
Worker 51 verified the target and dependency scope and expanded this
documentation; the only change to the supplied Lean file is its title comment.
Independent acceptance requires incremental Lake compilation, exact target
inspection with the allowed assumptions, semantic review, and publication.
Compilation or a shared draft alone establishes none of those later statuses.
