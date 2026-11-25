# Fibrewise central-isogeny assembly using flat subgroup finiteness

This derived internal module removes the finite-subgroup spreading input from
`FibrewiseCentralIsogenyAssembly`. It uses the proved finiteness theorem for a
flat locally quasi-finite closed subgroup of a multiplicative-type group.
The relative-centre statement and global kernel centrality remain explicit
hypotheses. This module does not prove the unconditional published criterion.
All declarations are in
`Langlands.GroupScheme.FibrewiseCentralIsogenyFiniteAssembly`, in every universe
`u`, over an arbitrary base scheme; no reducedness, noetherian or nonemptiness
hypothesis is imposed.

Let `G` and `H` be reductive group schemes over `S`, and let `f : G ⟶ H` have
surjective underlying scheme map. Suppose that the actual kernel of every
residue-field base change of `f` is finite over that residue field, and that
the full scheme-theoretic kernel inclusion `kernelι f` is central over `S`.
Also assume `ReductiveRelativeCenterStatement.{u}`.

`finite_kernel_of_central` proves finiteness of the full kernel over `S`.
The earlier fibrewise reduction gives flatness and local quasi-finiteness of
`f`. The actual kernel square is a pullback, so both properties hold for the
kernel structure map. The relative-centre hypothesis supplies a represented
scheme-theoretic centre `z : Z ⟶ G` with `Z` of multiplicative type.
`centralKernelFactor` factors the actual kernel inclusion through `z`, and
`centralKernelFactor_isClosedImmersion` makes this factor a closed subgroup
inclusion. The required separatedness follows from affineness of the
reductive target. The proved theorem
`RelativeMultiplicativeType.IsMultiplicativeType.isFinite_closedSubgroup`
then makes the kernel finite. This argument uses neither the spreading
statement nor a multiplicative-type assertion about the kernel itself.

`isCentralIsogeny_of_central_kernel` combines this finiteness with the
previously proved isogeny criterion under the same surjectivity and
finite-residue-kernel assumptions. The existing finite-presentation
cancellation lemma supplies local finite presentation of `f`, using the
smoothness of `G` and `H`. These facts and the supplied global centrality give
`IsCentralIsogeny f`.

`finiteFppfCover` constructs an actual singleton cover of the underlying scheme
of `H`. Its index type is `PUnit`, its member is the underlying scheme of `G`,
and its map is the underlying scheme morphism of `f`. It is a cover for
`Scheme.precoverage (@IsFinite ⊓ (@Flat ⊓ @LocallyOfFinitePresentation))`:
`isCentralIsogeny_of_central_kernel` supplies all three morphism properties,
and the assumed surjectivity supplies joint surjectivity. Thus it is a
finite faithfully flat cover locally of finite presentation. The construction
also applies to the empty base and to empty underlying schemes.

`criterion_of_kernelCentrality` concludes the exact unchanged
`ReductiveFibrewiseCentralIsogenyStatement.{u}` from the relative-centre
statement and an arbitrary-base kernel-centrality theorem. The latter must
prove centrality of the full kernel from reductivity, surjectivity and
finite central residue-field kernels. The forward implication is the earlier
base-change theorem for central isogenies. The reverse implication uses that
supplied centrality theorem and `isCentralIsogeny_of_central_kernel`.

The provenance is internal: the finite-cover construction packages the
actual morphism and the properties established by the two preceding lemmas;
the assembly composes proved kernel geometry with proved subgroup finiteness.
No additional source theorem is assumed in place of either remaining
structural hypothesis. The published target and its import closure are
unchanged. This module keeps the relative-centre and global kernel-centrality
hypotheses as premises; the Library proves the relative-centre statement as
`reductiveRelativeCenter` (module `RelativeCenterProof`), and
[`FibrewiseCentralIsogenyProof`](FibrewiseCentralIsogenyProof.md) proves the
published criterion through `GlobalKernelCentrality.criterion_of_artinianInput`.
