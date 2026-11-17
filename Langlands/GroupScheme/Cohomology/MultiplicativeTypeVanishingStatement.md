# Statement: low-degree regular cohomology of multiplicative-type groups

`MultiplicativeTypeLowDegreeVanishingStatement.{u}` says that for every commutative ring `R` in universe `u` and every actual group scheme `H` over `Spec R` satisfying the Library predicate `RelativeMultiplicativeType.IsMultiplicativeType H`, `HasVanishingLowDegreeCohomology H` holds.

Explicitly, take any `R`-module `M` in that universe and any natural action of actual affine-test points `H(A)` by `A`-linear automorphisms of `A ⊗[R] M`. Every natural one-cochain satisfying the inhomogeneous one-cocycle equation must be a coboundary of an actual base element `m ∈ M`. Every natural two-cochain satisfying the Hochschild two-cocycle equation must be the coboundary of a natural one-cochain. The precise equations and coefficient-extension conventions are in the imported `RegularCochains` pair.

There are no smoothness assumptions on `H`, no splitness assumption, no characteristic restriction, and no finiteness, freeness or projectivity assumption on `M`. Thus the scope includes nonsmooth groups such as diagonalizable groups with torsion characters in positive characteristic, and arbitrary quasi-coherent coefficients.

Source: Brian Conrad, *Reductive group schemes* (2014), Appendix B.2, Remark B.2.4, p.285, which states the vanishing of all positive Hochschild cohomology with quasi-coherent coefficients over an affine base. The present statement retains only degrees one and two, using the functorial cochain description and differential on pp.283–284. It encodes regular cochains on all affine test algebras through the tensor-product module functor attached to `M`. This is the affine-test form of the degree-one and degree-two cocycle/coboundary consequence; no derived-functor comparison theorem is asserted separately.

The relative multiplicative-type predicate is the existing one from Conrad Definition B.1.1. Its finite-type diagonalizable local models do not impose smoothness. This statement is a prerequisite for the square-zero homomorphism deformation argument and contains no homomorphism lifting conclusion itself. The Lean file is a proposition definition and supplies no proof.
