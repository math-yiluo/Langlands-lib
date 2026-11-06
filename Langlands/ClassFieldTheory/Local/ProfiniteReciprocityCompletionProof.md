# The profinite reciprocity completion

`Langlands.LocalClassField.profiniteReciprocityCompletion` proves exactly the
published proposition `ProfiniteReciprocityCompletion.{u}`. It quantifies over
every prime, every `PadicField.{u} p`, every supplied compatible topology `T`,
and every continuous homomorphism `r` satisfying
`GeometricProfiniteReciprocityRelation F T r`. The carrier universe is arbitrary.
The conclusion gives injectivity of `r` and the unique continuous group
equivalence from `LocalMultiplicative.profiniteCompletion T` to the actual
`Field.absoluteGaloisGroupAbelianization F.Carrier` agreeing with `r` on
`LocalMultiplicative.completionMap T`.

The proof first installs the supplied field topology, valued-field relation
and local-field structure. The existing `localAbelianGaloisGroup F` package
supplies compactness, Hausdorffness and total disconnectedness of the actual
absolute-Galois abelianization. The full geometric relation remains the
hypothesis; this deduction uses its `ProfiniteNormResidueRelation` component,
including density and the exact finite norm kernels.

For injectivity, `injective_of_normSubgroupsSeparatePoints` applies the proved
`normSubgroupsSeparatePoints`. A nonidentity element in the kernel would lie
in every finite norm subgroup by the exact finite kernels, whereas arithmetic
norm separation gives an actual finite abelian intermediate field whose norm
subgroup excludes it.

For the completion comparison,
`finiteQuotientDescent_of_normSubgroupExistence` applies the proved
`Langlands.ClassFieldTheory.Local.normSubgroupExistence`. Equality of the
supplied and canonical topologies transports this arithmetic theorem to every
actual open finite quotient of the supplied multiplicative topology. For
each quotient, an actual finite abelian intermediate field realizes its
kernel as a determinant-norm subgroup. Galois restriction, the inverse finite
norm-residue equivalence and the identity-induced quotient map give continuous
descent through `r`, with the required equation on original field units.

`ContinuousProfinite.existsUnique_equiv_of_finite_quotient_descent` now
extends `r` to the actual completion. Density of `r` makes the extension
surjective; descended finite quotient coordinates make it injective.
Compactness and Hausdorffness give continuity of the inverse. Density of the
completion map gives uniqueness. The completion and its map are the existing
closure-of-diagonal constructions using open finite quotients of the original
topology.

This proof is an internal derivation from the published arithmetic proofs,
norm-kernel bridges and generic completion comparison. It adds no hypotheses
to the target and does not require existence of a reciprocity map. Worker 1607
implements the arithmetic application and assembly; Worker 1556 supplies the
generic topological comparison in `CompletionComparison`. The imported
arithmetic proofs retain their authorship and provenance in their own paired
Markdown.
