# Relative-root reflections from explicit structural inputs

This internal construction works for arbitrary fields and universes, with the
actual connected reductive group, maximal split torus, integral character and
cocharacter lattices, rational normalizer points, and full scheme-theoretic
character kernels. It retains six structural propositions as hypotheses:

- `RelativeRoot.TorusActionUnipotenceStatement`;
- `DynamicConnectedStatement`;
- `SmoothMaximalSplitTorusConjugacyStatement`;
- `MinimalPseudoParabolicConjugacyStatement`;
- `RelativeRoot.KernelCentralizerComponentReductiveStatement`;
- `UnipotentFieldExtensionStatement`.

Under these hypotheses, `relativeRootReflectionExistence_of_structure` proves
the exact published proposition `RelativeRootReflectionExistenceStatement`.
This is a conditional theorem. None of the six structural hypotheses is
proved by this unit.

For each actual relative root `a`, the published
`RelativeRoot.kernelCentralizerStructure` supplies a smooth closed
representative `C → G` of the centralizer of the full character kernel.
Closedness in affine `G` gives affineness of `C`. The explicit component
reductivity hypothesis makes the actual identity component `C⁰` connected
reductive. The published ground-field radical theorem, applied with the
explicit preservation-of-unipotence hypothesis, makes its ground-field
unipotent radical trivial.

The opposing-parabolic construction in `RootKernelOppositeNormalizer` now
supplies an actual rational normalizer in `G` which centralizes the full
character kernel and negates `a`. Its other four structural inputs are exactly
the first four hypotheses above. The published integral coroot and
reflection-data assembly theorem then constructs reflection data for all actual
roots at once. The assembly also handles the empty root set. Centralization is
retained as membership in the all-test centralizer, including nonreduced test
schemes and arbitrary refinements.

`relativeRootReflectionDataOfStructure` chooses the resulting actual data.
The coroot at each root is an integral cocharacter pairing to two, and the
actual rational representative acts by its reflection formula on the whole
character lattice. `relativeRootReflectionDataOfStructure_mem` records
full-kernel centralization for every chosen representative.

The provenance is composition of the named full-kernel representability,
identity-component reductivity, ground-field radical descent,
opposing-parabolic normalizer, integral coroot and reflection assembly APIs.
The included unchanged `RootKernelIdentityWeights` pair was authored by
Worker 1339. No reduced or primitive kernel replacement, rational root-point
premise, or root-system classification premise is introduced. The host task
still requires proofs and publication of the six structural inputs before
this reduction can yield an unconditional proof of its target.
