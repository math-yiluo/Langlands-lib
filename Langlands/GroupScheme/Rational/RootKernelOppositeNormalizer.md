# Opposing-parabolic normalizers in full root-kernel centralizers

This internal construction works over an arbitrary field and universe with the
actual character lattice and full scheme-theoretic character kernel. Four
structural propositions remain explicit: torus-action unipotence, connectedness
of dynamic subgroups, smooth maximal-split-torus conjugacy, and minimal
pseudo-parabolic conjugacy.

`exists_moving_normalizer_of_cyclic_roots` starts with a smooth connected affine
group with trivial ground-field unipotent radical and a maximal split torus.
All actual roots must be integer multiples of the specified root, and the
specified cocharacter pairs positively with it. Use the canonical closed affine
representatives of the two opposing dynamic parabolics. The published
`dynamicSmooth` theorem makes both representatives smooth; the explicit
connectedness proposition makes them connected. The opposing-parabolic
normalizer construction then supplies an actual rational normalizer that moves
the specified root. No root-point or root-negation premise is needed.

For the remaining declarations, let `i : T → G` be a maximal split torus in an
affine group locally of finite type. Let `j : C → G` be a smooth affine closed
representative of the centralizer of the full kernel of an actual root `a`.
Assume that the ground-field unipotent radical of the actual identity component
`C⁰` is trivial. Smoothness, affineness and connectedness of `C⁰` are supplied by
the existing identity-component construction.

The existing lifted torus remains maximal split in `C⁰`. The complete integral
weight comparison identifies its roots with the ambient roots in `ℤ a`; in
particular `a` is still a root. Every component root is therefore an integer
multiple of `a`. The split-torus pairing theorem supplies an actual cocharacter
with positive pairing. Applying the preceding canonical-parabolic existence
theorem proves `exists_moving_kernelCentralizerIdentityNormalizer`. Classical
choice applied to this named existence proof gives
`kernelCentralizerIdentityOppositeNormalizer`.

`kernelCentralizerOppositeNormalizer` is its image under the actual inclusion
`C⁰ → C → G`. The published normalizer map preserves normalization of the
original torus and its action on the whole character lattice. Thus the image
still moves `a`. Its factorization through `C` proves centralization of the
full character kernel on every test scheme and every refinement.

The full-kernel divisibility theorem now shows that every character difference
is an integral multiple of `a`. The integral rank-one line theorem says that
an automorphism with this property fixes or negates the nonzero character `a`.
Movement excludes the first case, proving
`kernelCentralizerOppositeNormalizer_flip`. This argument needs neither a
primitive character nor smoothness of its kernel, nor a finite-order assertion
about the normalizer action. Finally the published integral coroot extraction
gives a unique actual cocharacter with self-pairing two and the reflection
formula for every character.

The provenance is composition of the named canonical dynamic subgroup,
cyclic-root normalizer, identity-component transport, full integral weight
comparison and integral coroot APIs. Worker 1339 authored the included unchanged
`RootKernelIdentityWeights` pair. This construction leaves its four structural
inputs and component radical triviality explicit. It does not prove the
unrestricted `RelativeRootReflectionExistenceStatement`.
