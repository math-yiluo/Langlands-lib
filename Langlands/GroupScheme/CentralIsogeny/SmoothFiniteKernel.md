# Centrality of smooth finite kernels

The module proves that a smooth finite homomorphism `f : G → H` over an
arbitrary field has central full scheme-theoretic kernel when `G` is smooth,
affine and connected. The field, source and target lie in one arbitrary
universe. There is no smoothness, affineness or connectedness assumption on
`H`. Smoothness of `f` is essential to the proof; the result does not cover
arbitrary inseparable isogenies.

Here centrality is the published `IsCentral (kernelι f)`. It asserts that
every point of the actual kernel over every test scheme commutes with all
source points after every further restriction. It is stronger than a
statement about the kernel of the homomorphism on ground-field points.

Over an algebraically closed field, the actual kernel is smooth by its
pullback square with `f`. Its product with `G` is smooth and therefore
reduced. The published finite-homomorphism cancellation lemma makes the
rational kernel points central among rational source points. Apply this to
the two projections of a rational point of the product: its commutator is
the identity. The published rational-point extensionality theorem then
identifies the actual commutator morphism with the identity morphism.
Evaluating that equality on arbitrary test schemes gives full kernel
centrality.

For an arbitrary field, pull back to its algebraic closure. Smoothness,
affineness and finiteness survive base change; connectedness survives this
base change for a smooth connected affine group. The algebraically closed
result therefore applies to the actual pulled-back homomorphism. Published
fpqc reflection of kernel centrality descends the conclusion along the
faithfully flat field extension.

This is an internal derivation from the Library's actual kernel, smooth
product, rational-point density, finite-homomorphism cancellation and fpqc
reflection results. The paired proof implements this argument directly and
does not import the conclusion of the fibrewise-isogeny rigidity statement
`StrictHenselianDVRIsogenyRigidityStatement`, whose proof in
`Reductive.SpecialFibreIsogenyRigidity` uses this module.
