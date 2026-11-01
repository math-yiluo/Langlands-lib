# Quasi-coherence and finite affine sections under abelian constructions

This internal helper develops closure properties needed by the coherent support induction.
It defines `HasFiniteAffineSections M` to mean that the actual module of sections
`Γ(M, U)` is finite over `Γ(X, U)` for every affine open `U`. This is the finite-section
hypothesis used by the published proper coherent cohomology finiteness statement.

Quasi-coherence on every affine open implies global quasi-coherence: first transport from
the affine spectrum to the open subscheme by the affine isomorphism, then across the
equivalence with the slice site, and use the open covering locality of quasi-coherence.
The slice-site transport uses the actual equivalence of sheaf-module categories and its
identification of the unit sheaf, so it preserves local presentations.

Global quasi-coherence is stable under kernels, cokernels, images, binary direct sums,
and pushforward along affine morphisms. The kernel, cokernel, and pushforward results
use the existing affine-local closure lemmas followed by the locality theorem above.
Images are identified with kernels of cokernels. On an affine spectrum the direct-sum
result follows from the tilde functor's preservation of binary biproducts and the
quasi-coherent tilde–sections isomorphism. Restriction preserves biproducts, giving the
general direct-sum result.

An epimorphism of quasi-coherent modules is surjective on sections over any affine open.
On a spectrum, naturality of the tilde–sections comparison and its invertible components
make the tilde image of the section map an epimorphism. The fully faithful tilde functor
reflects epimorphisms, so the section map is surjective. Restricting to the spectrum of
an affine open, then transporting along the restriction-section isomorphism, gives the
claim on that open. There is no assertion of surjectivity on arbitrary nonaffine opens.

Finite affine sections are invariant under isomorphism and stable under binary direct
sums. Evaluation gives the required linear isomorphisms, and the evaluated biproduct is
the product of two finite modules. Over a locally noetherian scheme they pass to
submodule sheaves, kernels, and images: the affine coordinate ring is noetherian, a
monomorphism is injective on sections, and a submodule of a finite module over that
ring is finite. No quasi-coherence is needed for these submodule conclusions.
For epimorphisms between quasi-coherent modules they pass from source to target by
the affine section-surjectivity result. In particular, the cokernel of a map of
quasi-coherent modules has finite affine sections when its target does.

The provenance is internal. These are derived closure lemmas for the actual Mathlib
categories of scheme modules, using the existing `QuasicoherentLocal.Closure` and
Mathlib's tilde adjunction, sheaf locality, abelian images, and noetherian module
finiteness. They prepare coherent support induction but assert neither Euler
polynomiality nor positivity of a leading coefficient.
