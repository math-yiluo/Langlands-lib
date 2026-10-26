# Finite continuous coefficients for enveloping conjugation

Author: Worker 566.

This proof targets the published internal proposition
`Langlands.Global.ArchimedeanGL.EnvelopingConjugationCoefficientsStatement`.
The theorem
`Langlands.Global.ArchimedeanGL.envelopingConjugationCoefficients` in module
`Langlands.Global.ArchimedeanAdjointCoefficientsProof` proves it for every
`K : Type u` with `[Field K] [NumberField K]` and every `n : ℕ`.
It uses the actual completion-based group, its existing topology, and the
existing universal enveloping conjugation. Its algebra and topology argument is
derived internally from the imported constructions and Mathlib's finite
dimensional linear algebra, tensor products, and algebra generation.

The proof first establishes closure of finite continuous expansions under
addition, multiplication, and complex scalar multiplication. Addition joins
the two finite indexing types; multiplication takes their product and multiplies
the coefficient functions pointwise. Finite indexing types are reindexed by
`Fin m`, without changing the represented sum.

For a real Lie generator, choose a finite real basis of the actual mixed
archimedean matrix space. For fixed `X`, the map `g ↦ g X g⁻¹` is continuous
in the existing group coordinates: the coordinate equivalence, units value,
group inverse, and matrix multiplication are continuous. Each real basis
coordinate is continuous by finite dimensionality, and its inclusion into the
complex numbers is continuous. Apply the real linear map from matrices through
the real Lie algebra, complexification, and the canonical enveloping generator
to the basis expansion. These give a fixed finite family of enveloping
elements and globally continuous coefficient functions.

Tensor induction extends this to every complexified Lie generator. Quotient
induction and tensor algebra induction then extend it to every enveloping
element using the closure properties and the scalar case. The family and
coefficient functions are chosen before the group variable. No topology on the
enveloping algebra is introduced. The finite matrix basis may have zero
elements, so the same argument includes rank zero without an additional
assumption.
