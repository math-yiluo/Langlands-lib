# Finite projective coefficients and arbitrary product tensors

This derived algebraic construction supports the finite-level product
comparison in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed pages 9–10. The actual S-integer extension there
is finite locally free, whereas an adelic level contains an infinite product
of original local coefficient rings. This unit specializes an existing
Library tensor comparison and packages its canonical map as an algebra
equivalence.

For any commutative ring R, finite projective R-module M, arbitrary index
type, and family of R-modules N, `finiteProjectivePiTensorMap_bijective`
proves bijectivity of the existing canonical `TensorProduct.piRightHom`.
This map sends m tensor a tuple to the tuple of m tensor each component.
The proof works with additive groups and the specified module actions.

Mathlib's `Module.finitePresentation_of_projective` supplies finite
presentation from the finite and projective hypotheses. The published
`RestrictedProduct.tensorPiComparison_proof`, imported from
`Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof`, then proves
bijectivity of exactly this map. That general result applies to arbitrary
finitely presented modules and arbitrary product index types. This unit
reuses it without reconstructing its finite-presentation or finite-free
argument.

For commutative R-algebras B and C indexed by an arbitrary type, with B finite
projective over R, `finiteProjectivePiTensorEquiv` packages the canonical
`Algebra.TensorProduct.piRightHom` as a B-algebra equivalence. Its pure-tensor
formula retains exactly the original B coefficient and each original tuple
component. The product index need not be finite, and none of the C factors
needs to be finite or projective.

The base ring, coefficient module or algebra, product index, and product
factors may inhabit independent arbitrary universes. There are no field,
domain, Noetherian or topological hypotheses. This is generic derived
coefficient infrastructure for the source's finite locally free extension;
its actual adelic-level arithmetic instantiation and point homeomorphisms
remain obligations of the host task.
