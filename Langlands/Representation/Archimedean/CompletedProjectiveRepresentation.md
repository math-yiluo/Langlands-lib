# Completed projective tensor products of Banach representations

`Carrier` is the completion of the algebraic projective tensor product of a finite family of complex normed spaces. `pure` is its continuous multilinear pure tensor map. `lift` extends a bounded multilinear map into any complex Banach space and computes the original map on pure tensors.

`CompletedProjectiveRepresentationStatement` concerns a finite family of jointly continuous complex Banach representations of a locally compact group with a real manifold model. Completing the induced diagonal operators gives a representation on `Carrier`. It is jointly continuous, and a pure tensor of genuine smooth vectors has a genuine smooth orbit for this representation.

Mathlib's projective seminorm and `PiTensorProduct.mapL` give the diagonal operators on the algebraic tensors. Equality on the dense algebraic image gives the composition law and the operator-norm bound on the completion. Continuity on pure tensors follows from continuity of the factor orbits and of `pure`. Tensor induction extends it to algebraic tensors. On a compact group neighborhood, Banach–Steinhaus bounds the factor operator norms. The product bound and density of algebraic tensors give joint continuity of the completed action. For a pure smooth input the orbit is the composition of the finite tuple of smooth factor orbits with the real smooth multilinear map `pure`.

This construction provides a Banach tensor representation for applying smooth-vector averaging to diagonal actions. Jacquet, *Archimedean Rankin–Selberg Integrals*, §2, pp. 4 and 9, and Lemma 14.1, p. 106 in the author-posted edition, uses projective tensor products and diagonal smoothing in the ordinary local integral argument.
