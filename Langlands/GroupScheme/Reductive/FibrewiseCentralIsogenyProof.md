# The fibrewise central-isogeny criterion for reductive group schemes

The theorem `Langlands.GroupScheme.reductiveFibrewiseCentralIsogeny`
proves the unchanged published proposition
`Langlands.GroupScheme.ReductiveFibrewiseCentralIsogenyStatement`.
For a surjective homomorphism between reductive group schemes over any
scheme, it is a central isogeny if and only if every canonical residue
fibre has finite central scheme-theoretic kernel. All schemes and rings
range over an arbitrary universe `u`. No structural proposition or
additional hypothesis remains as an argument to the theorem.

The implemented proof first discharges
`NoetherianKernelCentrality.FiniteFlatArtinianKernelCentralityStatement`.
Let the base be the spectrum of a commutative local Artinian ring `R`,
and take the actual kernel `N` of a homomorphism `f : G → H` satisfying
that proposition's premises. The given finiteness of `N` over `R`
makes it affine. Flatness of `f` and the actual kernel pullback square
make `N` flat. Reductivity makes the ambient group `G` affine and the
target `H` separated.

Write `k = IsLocalRing.ResidueField R`. The field theorem
`CentralResidueKernelMultiplicativeType.isMultiplicativeType_kernel_fieldFiber`
gives absolute multiplicative type of the unchanged pullback `N_k`
along `Spec.algebraMap R k`. Its hypotheses are reductivity of `G`,
separatedness of `H`, and centrality of every actual canonical residue
kernel. The canonical kernel base-change comparison converts that last
centrality into centrality of the pulled-back original inclusion.
`CentralResidueKernelMultiplicativeType.isCentral_field_baseChange_of_residue`
then gives centrality of that inclusion along the same map `Spec k → Spec R`.
This uses the actual field pullback and does not replace the kernel by
its reduced subgroup.

Apply
`FiniteFlatArtinianCentrality.isCentral_of_multiplicativeType_residue`
to `N → G` with these two residue inputs. Its finite affine flat source
and affine target requirements have just been established, so it gives
all-test centrality of the original kernel inclusion over `R`. This
proves the focused local Artinian proposition without a retained input.

Finally, `GlobalKernelCentrality.criterion_of_artinianInput` applies
to this proved local proposition. That reduction transports actual
residue-kernel centrality through base change, uses noetherian
approximation and Artinian detection on affine bases, and glues
centrality over an arbitrary base's affine open cover. Its assembly
uses the reductive relative centre and the finite flat quasi-finite
subgroup finiteness result to obtain the central isogeny. The forward
implication is the existing base-change argument for central isogenies.
Its conclusion is exactly the published equivalence.

The proof composes these established mathematical results with the
explicit actual-kernel application above. The target statement and its
imports are unchanged. The structural splitting, nilpotent lifting and
infinitesimal centrality development used by the Artinian theorem is
imported through `Torus.FiniteFlatArtinianCentrality`.
