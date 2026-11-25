# Finite projective coefficients and arbitrary product tensors

This derived algebraic construction supports the finite-level product
comparison in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), Example 4.2, printed pages 9–10. The actual S-integer extension there
is finite locally free, whereas an adelic level contains an infinite product
of original local coefficient rings. This module specializes an existing
Library tensor comparison and packages its canonical map as an algebra
equivalence.

For any commutative ring R, finite projective R-module M, arbitrary index
type, and family of R-modules N, `finiteProjectivePiTensorMap_bijective`
proves bijectivity of the existing canonical `TensorProduct.piRightHom`.
This map sends m tensor a tuple to the tuple of m tensor each component.
The proof works with additive groups and the specified module actions.

Mathlib's `Module.finitePresentation_of_projective` supplies finite
presentation from the finite and projective hypotheses. The published
`Langlands.LinearAlgebra.RestrictedProduct.tensorPiComparison_proof` (named
`RestrictedProduct.tensorPiComparison_proof` until 22 November 2026), imported from
`Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof`, then proves
bijectivity of exactly this map. That general result applies to arbitrary
finitely presented modules and arbitrary product index types. This module
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
are left to the proof of the statement this module serves,
`AdelicProjectiveWeilComparisonStatement` (Example 4.2), which the Library
proves as `adelicProjectiveWeilComparison` in `AdelicProjectiveWeilComparisonProof`.
