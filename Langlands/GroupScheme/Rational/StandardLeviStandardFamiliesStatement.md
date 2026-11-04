# Actual standard families inside a represented standard Levi

Author: Worker 189. This is a derived internal comparison supporting the rational-point Howe implication in task `03a0d235-af42-49a9-bee7-7d971c0dcc4a`.

`Langlands.GroupScheme.StandardLeviStandardFamiliesStatement` is a proposition at the arbitrary field universe `u`. It assumes the published propositions `DynamicLieStatement` and `StandardCocharacterStatement`. For a connected reductive group scheme `G` over any field `k`, an actual maximal split torus `i : T → G`, a generic cocharacter `ν`, and any subset `J` of the actual simple relative roots, it considers any connected reductive group scheme `L` represented as the actual choice-free standard Levi of `J` by a closed subgroup map `j : L → G`.

For the canonical torus factor `iL = standardLeviTorusFactor i ν J hj`, the statement asserts all of the following:

- The actual simple relative roots of `iL` with respect to the same `ν` equal exactly `J`, as subsets of the same character lattice of `T`.
- The same `ν` is generic for `iL`.
- For every character subset `K ⊆ J`, each of `standardParabolic iL ν K`, `standardLevi iL ν K`, and `standardUnipotent iL ν K` is the inverse image under `j` of its corresponding ambient standard subgroup functor. The equalities hold on all test schemes, not only on rational points.

The empty subset and empty root system are included. There is no reducedness assumption, no restriction on the characteristic, and no general-linear specialization. Connected reductivity of the representative `L` is an explicit hypothesis; this comparison does not construct or establish reductivity of standard Levis. The two global structural statements also remain explicit antecedents.

The provenance is internal. The formulation connects the already published torus factor, actual adjoint-weight definition of relative roots, dynamic Lie proposition, and choice-free standard subgroup functors. It is the structural comparison needed before applying `CuspidalityTransport` to identify literal inside-Levi cuspidality with cuspidality for the Levi scheme's own standard family. The statement itself makes no assertion about representations, compact coefficients, finite restriction to a norm kernel, or the final Howe theorem.
