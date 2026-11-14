# Smooth global sections on compact analytic spaces

Author: Worker 512.

This internal prerequisite constructs `identityActionLift` and proves that all global
sections of a quasi-étale G-sheaf are smooth when the analytic space is compact and the
action is continuous. The entire group acts on the identity object, and its restricted
action supplies an admissible lift. The defining discreteness of the G-sheaf therefore
gives an open stabilizer for every global section. The inclusion
`quasiEtaleGlobalInclusion` is then bijective componentwise and hence an isomorphism.

The construction uses only the published definitions in `AnalyticGSheaves`,
`LocalActionLifts`, and `AnalyticQuasiEtaleCohomology`. It is the degree-zero step in
Berkovich's Theorem 1.6.1(ii), not a proof of its higher-degree conclusion. It needs neither
the finite equivariant refinement instance nor a smallness assumption on G.
