# Relative multiplicative-type kernels from rigidity and monomorphism spreading

Worker 879, using the unchanged same-task explicit quotient constructions
of Worker 886. Internal derived reduction of the full relative kernel
criterion.

`isMultiplicativeType_kernel` proves the following conditional result,
in every universe. Supply proofs of the **exact** published statements
`MultiplicativeTypeCentralRigidityStatement` and
`MultiplicativeTypeMonomorphismSpreadingStatement`. For any scheme `S`,
group schemes `H`, `G`, and homomorphism `f : H → G`, assume:

- `H` is of relative multiplicative type;
- `G` is separated over `S`;
- `S` is locally noetherian, or `G` is locally of finite presentation,
  quasi-compact and quasi-separated over `S`.

Then the actual scheme-theoretic kernel of `f` is of relative
multiplicative type. These are precisely the hypotheses and kernel
conclusion in the published canonical-factorization target. The two
rigidity and spreading statements remain explicit premises; this
module does not assert either of them unconditionally.

For a split source `D_S(M)`, the implementation extends the full kernel
of the residue fibre at `s` as a closed subgroup `D_S(N)` using
`MultiplicativeTypeKernelFibreModel`. Its composite with `f` is trivial
on that fibre. Clause 5.2 of the supplied exact rigidity statement
makes it trivial over an open neighborhood `W`.

The explicit exact quotient of `D_S(M)` by this extended subgroup
restricts to `W`. The full fibre-kernel equation is transported to
the residue fibre at the corresponding point of `W`. The implemented
transport first base changes along the residue-field map, then
compares iterated base change along the canonical equation of the two
residue-fibre morphisms. It therefore preserves the full subgroup
functors on every test scheme.

`MultiplicativeTypeKernelNeighborhood.exists_neighborhood` applies
clause 6.6 of the supplied exact spreading statement to the quotient
factor and identifies the actual kernel with the extended subgroup
on a smaller neighborhood. `splitKernelOpenCover` chooses these
actual open-immersion neighborhoods at all points. It has type
`KernelOpenCover f`, recording both the cover and multiplicative type
of the full kernels on its members. Fppf locality of relative
multiplicative type, together with the actual kernel base-change
isomorphism, yields the split-source criterion.

For the general source, choose its diagonalizing fppf cover.
Locally finite presentation of the cover maps preserves local
noetherianness when the base is locally noetherian; otherwise all
three target finiteness properties persist by base change.
Transport the homomorphism through the actual diagonalizable
source isomorphism, apply the split-source result, and descend the
kernel property by fppf locality.

The auxiliary `kernelBaseChangeCompIso` and range-transport lemmas
use the published `kernelSquareIso` and
`KernelRepresentative.iso`. All declarations are derived content
assembled from the cited Library constructions. The final canonical
quotient/factorization step is outside this module.
