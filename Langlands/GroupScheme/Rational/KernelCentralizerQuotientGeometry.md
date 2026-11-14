# Full kernels of character-kernel centralizer quotients

This internal supporting construction proves the full kernel geometry of the
actual restriction between identity components of represented character-kernel
centralizers. It works at arbitrary universe `u` over a perfect field `k`.

Let `i : S → G` be a homomorphism from a split torus and let `a` be any character
of `S`. Let `q : G → H` be a homomorphism of affine group schemes whose actual
scheme-theoretic kernel is smooth, connected and unipotent. Suppose the full
centralizers of the entire scheme-theoretic kernel of `a` are represented by
`jC : C → G` and `jE : E → H`, with `C` and `E` smooth affine and `jC` closed.
The character may be zero or nonprimitive, and its kernel need not be smooth.
Neither ambient group is assumed reductive. The target representative is not
required to be closed.

`kernelCentralizerIdentityMap_kernel_geometry` proves that the full actual
kernel of the existing map
`kernelCentralizerIdentityMap i a q hC hE : C⁰ → E⁰`
is smooth, connected and unipotent. If the ambient groups are smooth and `q`
is smooth, `kernelCentralizerIdentityQuotient` returns that same map in a subtype
recording its smoothness, scheme surjectivity and full kernel geometry.
Its underlying map is definitionally the existing restriction, so the ambient
and original-torus squares of `SmoothKernelCentralizerQuotient` apply unchanged.

The proof first handles the restriction `C → H`. The ambient full kernel
`N = ker(q)` is invariant under conjugation by the original torus, on every
relative scheme test. `conjugation_kernel_isStable` verifies this directly by
applying `q` to the conjugation formula. The represented-subgroup action API
therefore gives an actual action of `S` on `N`.

The full kernel `K = ker(jC ≫ q)` has a closed inclusion `t : K → N` from
`SectionedSubgroupKernel.toAmbientKernel`. Its full range is exactly the fixed
subgroup of the restriction of this action along `characterKernelι a`.
`RepresentedActionFixed` supplies this identification as the inverse image of
the ambient fixed functor. The actual diagonalizable model
`D(X*(S)/ℤa)` and `Diagonalizable.FixedSmooth.fixedSubgroupSmooth` then prove
that `K` is smooth, including when the character kernel is nonreduced.

Perfectness and the smooth connected unipotence of `N` give a split unipotent
series, hence the uniform all-test solvability required by
`Torus.solvableFixedContainmentConnected`. The fixed subgroup of the restricted
action is invariant under the whole commutative torus and contains its whole
fixed subgroup. That theorem proves `K` connected. The closed inclusion into
the unipotent group `N` proves `K` unipotent. This is
`kernelCentralizerMap_fullKernel_geometry`; it does not require smoothness of
`C` or either ambient group.

Connectedness now factors the full kernel inclusion `K → C` through the
ordinary identity component `C⁰`. The proof verifies on every test scheme that
this factor represents precisely the full kernel of `C⁰ → E⁰`: the existing
ambient square and the monomorphic inclusion `E⁰ → H` detect the kernel
equation. `KernelRepresentative` transports all three geometric properties
from `K` to the actual kernel.

The provenance is internal composition of the named existing Library results.
No new original-literature reformulation is asserted. This unit supplies
quotient kernel geometry; it does not prove integral opposite factors or the
descended facet root-datum theorem.
