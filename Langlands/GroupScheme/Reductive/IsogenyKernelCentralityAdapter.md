# From full-kernel torus containment to ambient centrality

This derived construction combines actual kernel factorization, generic
centralizer comparison, and the published centrality theorem for a split-torus
kernel through which every root factors.

Over any base, consider a commuting square from a map between commutative group
schemes to an ambient group-scheme map, with monomorphic target inclusion.
Given an actual factorization of the ambient kernel through the source
commutative group, its image is killed by the restricted map: composing with the
target inclusion gives the zero-on-points ambient composite, and monicity
cancels the inclusion. The representing group scheme of the restricted kernel
therefore gives `kernelRestrictionFactorOfTorusFactor`. Its composite with the
restricted kernel inclusion is the supplied factor, and its composite with both
inclusions is the original ambient kernel inclusion.

If the restricted kernel maps centrally into the ambient source, precomposing
by this comparison map proves centrality of the full ambient kernel. All these
assertions use the actual scheme-theoretic kernels and quantify over all test
schemes.

Over a field, the source is connected reductive, the target group scheme is
affine, and the ambient homomorphism is finite. The source contains a supplied
split maximal torus and generic integral cocharacter. The published
`maximalTorusCentralizer` identifies the full torus centralizer with the torus
range. The published `genericCentralizer` identifies the dynamic centralizer
with that centralizer. Trivial kernels on the two opposite dynamic unipotents
then give `kernelTorusFactorOfGenericUnipotentKernels`, with its exact composite
identity, by the preceding full-kernel containment construction.

For a map to another split torus in a commuting ambient square with closed target
inclusion, assume every source root is the actual character pullback of some
target-torus character. The published
`isCentral_kernelι_comp_of_roots_comapHom` proves centrality of the full restricted
torus kernel, including its infinitesimal structure. The kernel comparison just
constructed therefore proves centrality of the entire ambient kernel.

The field construction assumes an affine target and a finite ambient map.
The two opposite unipotent kernel
conditions, genericity, and exact root pullback condition remain explicit
inputs. The result neither derives those conditions from characteristic-power
root factors nor proves the complete root-datum comparison. No reducedness or
smoothness of either kernel, target genericity, or separability is assumed.
