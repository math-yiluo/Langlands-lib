# Kernel geometry and assembly for the fibrewise central-isogeny criterion

Worker 625.

This internal construction is derived from the kernel and multiplicative-type
steps in Conrad, *Reductive group schemes* (2014), Proposition 3.3.10, p.103.
It does not give an unconditional proof of that proposition. The relative-centre
theorem and the finite-subgroup spreading theorem are explicit hypotheses of
the finiteness and assembly results. Global centrality is also an explicit
hypothesis, rather than a conclusion from residue fibres.

The declarations are in
`Langlands.GroupScheme.FibrewiseCentralIsogenyAssembly`, in every universe `u`.

`centralKernelFactor` constructs the actual factor of a central full
scheme-theoretic kernel through a supplied full scheme-theoretic centre.
It uses the universal property of the represented all-test centre functor.
`centralKernelFactor_comp` proves that its composite with the centre inclusion
is the actual kernel inclusion. If the target of the original homomorphism is
separated, `centralKernelFactor_isClosedImmersion` obtains a closed immersion:
the kernel inclusion is closed and closed immersions cancel on the right.

`locallyOfFinitePresentation_hom` applies the existing finite-presentation
cancellation theorem: the source structure map is locally of finite
presentation and the target structure map is locally of finite type.
Smoothness supplies both facts. `locallyOfFinitePresentation_kernel` pulls
back this property along the unit section using the actual kernel square.
Neither argument assumes that the base is noetherian.

`finite_baseChanged_kernel` transports finiteness across the canonical
isomorphism between base change of the actual kernel and the actual kernel of
the base-changed homomorphism.

`finite_kernel_of_central` assumes
`ReductiveRelativeCenterStatement` and
`MultiplicativeTypeFiniteSubgroupSpreadingStatement`.
The first supplies a closed relative centre of multiplicative type.
The actual kernel factors into that centre as a closed subgroup, is locally of
finite presentation by the preceding lemma, and is affine over the base
because it is closed in the affine source. Affineness supplies
quasi-compactness and quasi-separatedness. Its finite residue fibres therefore
allow the finite-subgroup spreading theorem to give finite restrictions over
an open neighbourhood of every base point. Finiteness is local at the target,
so these restrictions imply global finiteness.

`isCentralIsogeny_of_central_kernel` combines this conditional finiteness with
the previously proved fibrewise reductions. Surjectivity and finite residue
kernels give an isogeny once the actual kernel is finite. The local finite
presentation lemma and the supplied global centrality complete
`IsCentralIsogeny`.

`criterion_of_kernelCentrality` packages both implications into the exact
published criterion, conditionally on the two named structural statements and
an arbitrary-base kernel-centrality theorem. The latter takes the original
surjectivity, reductivity and finite central residue-kernel hypotheses and
concludes centrality of the actual global kernel. The forward direction uses
the previous module's base-change result. The reverse direction applies
`isCentralIsogeny_of_central_kernel`.

The structural hypotheses are still separate proof obligations in the
Library. This module neither asserts them nor changes the published
`ReductiveFibrewiseCentralIsogenyStatement`.
