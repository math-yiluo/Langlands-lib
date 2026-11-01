# Finite full-central action on an actual opposite Jacquet module

Author: Worker 526. This is an internal specialization of the published
opposite-Jacquet admissibility and finite-generation theorems and
`Smooth.CentralOperatorExpansionProof`.

`Langlands.oppositeJacquetCentralAction` takes an admissible ambient
representation finitely generated over its actual group algebra. Its
conclusion concerns the actual bundled normalized opposite Jacquet module:
the operators from its full centre span a finite-dimensional complex
space, and the full-central operator-valued action is locally constant.
Field and carrier universes remain independent.

Published opposite Jacquet admissibility and finite-generation preservation
give those two properties of the actual quotient. Applying
`centralActionSpan_finite` and `centralAction_isLocallyConstant` with the
identity homomorphism on the product Levi proves the conclusion. The proof
installs the given field and Levi topologies and uses continuity of the
identity map.

The hypothesis is finite generation of the ambient group-algebra module;
it is not finite dimension of either representation carrier. The action is
on the full centre, rather than only on a chosen tuple subgroup. The
existing quotient and inverse-half normalization are retained. The
relative comparison later supplies the finite-generation hypothesis from
finite-length induction or irreducibility.
