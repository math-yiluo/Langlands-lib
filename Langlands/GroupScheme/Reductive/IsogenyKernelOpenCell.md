# Finite kernels in cells containing a self-centralizing torus

This is an internal geometric reduction for the actual general-isogeny root-datum
comparison. It is derived from the published finite-homomorphism torus-centralizer
reflection theorem and the actual scheme-theoretic kernel and base-change interfaces.

Over an algebraically closed field, every point of a finite kernel is closed and hence
comes from a point over the base field. Its image under the finite map is the identity,
so `mem_torusCentralizer_of_finiteHom` puts it in the source torus centralizer.
Self-centralization puts that point in the torus. Any supplied morphism through which
the torus inclusion factors therefore contains the topological image of the kernel.
The kernel is not assumed smooth or reduced.

The algebraically closed theorem's name anticipates its use for an open cell.
Its stated topological containment in fact holds for every supplied morphism
containing the torus inclusion.

`range_kernelι_subset_openCell` treats an arbitrary field and requires that the
supplied map `c : C ⟶ G.X` be an open immersion. Base change to the algebraic
closure preserves finiteness of the ambient map and torus self-centralization.
The algebraically closed result and the open-immersion lifting property give a
factorization of the full base-changed kernel. The canonical
`kernelBaseChangeIso` identifies this kernel with the base change of the original
kernel, compatibly with their inclusions into the ambient groups. The pullback
adjunction produces a factorization after the surjective projection from the
base-changed original kernel. Surjectivity of this projection then proves the
required topological containment over the original field.

`kernelOpenCellLift` applies the open-immersion lifting property once more to give
an actual morphism from the entire original kernel scheme to `C`.
`kernelOpenCellLift_fac` proves that its composite with `c` is exactly the
scheme-theoretic kernel inclusion. Thus the result includes nonreduced kernel
structure and applies on every test scheme. Field-valued points are used only
to establish topological containment over the algebraic closure.

The assumptions are a finite group-scheme homomorphism over any field, a torus
homomorphism whose full subgroup-functor centralizer equals its pointwise range,
and a specified factorization of that torus homomorphism through `c`. The ambient
map need not be flat or surjective, and the ambient groups need not be reductive,
connected, smooth or affine. The statement does not supply the open cell,
prove that the kernel lies in the torus, or establish the remaining root-datum
comparison. Those are separate inputs or subsequent steps.
