# Full logarithmic coordinates for number-field units

For a number field `E : Type v`, this module uses the actual group `(𝓞 E)ˣ`
and the real function space on `NumberField.InfinitePlace E`. There is no
Galois or cyclicity assumption.

`infiniteLogSum E` is the real linear map `x ↦ ∑ w, x w`, and
`fullLogHyperplane E` is its kernel. `mem_fullLogHyperplane` identifies
membership with the equation `∑ w, x w = 0`.

The additive homomorphism `fullLogEmbedding E` has domain `Additive (𝓞 E)ˣ`.
For a unit `x`, its coordinate at `w` is
`(mult w : ℝ) * Real.log (w (x : E))`. Mathlib's infinite places use the usual
absolute values; `mult w` is one at a real place and two at a complex place.
Consequently this is the logarithm of `w (x : E) ^ mult w`, the archimedean
absolute value with product-formula normalization. In particular the hyperplane
equation has an unweighted sum: the multiplicities are already in the coordinates.

`fullLogEmbedding_mem` proves that these coordinates sum to zero, using
`NumberField.Units.sum_mult_mul_log`. That imported theorem follows from the
product of the infinite-place absolute values, counted with multiplicities,
being the absolute rational norm, which is one for a ring-integer unit.
`fullLogEmbeddingToHyperplane` restricts the codomain accordingly.

`fullLogHyperplaneEquiv E` is a real linear equivalence from the hyperplane to
Mathlib's `NumberField.Units.dirichletUnitTheorem.logSpace E`. Its forward map
forgets Mathlib's chosen distinguished place `w₀`. Its inverse sets the coordinate
at `w₀` to the negative sum of the other coordinates. Splitting a finite sum
into the distinguished coordinate and the remaining subtype proves that this
inverse lies in the hyperplane and gives both inverse identities. The
construction also covers a field with only one infinite place: the remaining
coordinate set is empty.

`fullLogHyperplaneEquiv_apply` records the forward coordinate formula, and
`fullLogHyperplaneEquiv_log` proves that this equivalence carries the restricted
full logarithm exactly to `NumberField.Units.logEmbedding E`. The latter equality
is definitional. `fullLogEmbedding_eq_zero_iff` and `fullLogEmbedding_ker` identify
the full logarithm's kernel with `NumberField.Units.torsion E`, using Mathlib's
kernel theorem in one direction and its characterization of torsion units by
absolute value one at every infinite place in the other.

The mathematical source is J. S. Milne, *Class Field Theory*, v4.03 (2020),
Chapter VII, proof of Proposition 3.1, printed p.209 (PDF p.218), specialized
to the set of all infinite places. That passage defines the full logarithm,
identifies its kernel with roots of unity, and places its image in the
coordinate-sum-zero hyperplane. Milne's normalized-absolute-value convention is
stated in Chapter V, §4, printed p.169 (PDF p.178). The exact coordinate
comparison with Mathlib's omitted-place space is an internal construction,
not an additional assertion attributed to Milne.

The implementation reuses the pinned Mathlib modules
`Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`,
`Mathlib.NumberTheory.NumberField.Units.Basic`, and
`Mathlib.NumberTheory.NumberField.InfinitePlace.Basic`; in particular the
definitions of `logSpace`, `logEmbedding`, and `mult` are unchanged.
This prerequisite supplies the full-coordinate map, its linear coordinate
comparison, and the kernel identity. It does not establish Galois equivariance,
lattice discreteness or spanning, a cohomology formula, or the global
idele-class Herbrand theorem.
