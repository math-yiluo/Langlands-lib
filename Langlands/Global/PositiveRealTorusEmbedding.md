# Positive-real embedding in an actual split adelic torus

Worker 112, using the actual-point topology support by Worker 94.
This is an internal topological comparison of existing constructions. It
uses the general split-torus coordinate homeomorphism and the proved
closed embedding of positive scalar ideles.

Let `F` be a field, `I : Type u` a finite index type with a `Fintype`
instance, `T` an actual commutative group scheme over `Spec F`, and
`e : T.toGrp ≅ splitTorus (Spec F) I` an actual group-scheme isomorphism.
For every commutative `F`-algebra `A` with a topology making it a
topological ring, `coordinatesHomeomorph F I T e A` bundles the existing
`coordinates F I T e A` as a multiplicative homeomorphism from the actual
scheme-point carrier `Lie.AffinePoints T.toGrp A` to `I → Aˣ`.

The source has the existing topology induced by all regular-function
evaluations. A local instance merely exposes this same topology on the
`Lie.AffinePoints` alias. The target has the existing product topology on
units. Forward continuity follows from continuous postcomposition by
`e.hom` and continuity of split-torus coordinates. The theorem
`coordinates_symm_apply` identifies the inverse with inverse split-torus
coordinates followed by postcomposition by `e.inv`; these maps are
continuous. Forward continuity only requires a topology on `A`; the
inverse uses its topological-ring structure. No continuity assumption on
the base algebra map or Hausdorff hypothesis is added.

If `F` is a number field, `isClosedEmbedding_full` proves that the original
homomorphism

`full F I T e : (I → ℝ≥0ˣ) →* Lie.AffinePoints T.toGrp (Adeles F)`

is a closed topological embedding. Its formula is the product of the
existing positive scalar idele maps followed by the inverse coordinate
homeomorphism. The product scalar map is a proved closed embedding, and
the inverse coordinate homeomorphism is a closed embedding; their
composition gives the result. The scalar map retains the convention of
equal positive values at every infinite place and identity values at
finite places. The empty index type is included.

`continuousFull` bundles exactly this existing homomorphism with its
proved continuity. Existing character formulas, subgroup image and
intrinsic splitting-independence statements therefore continue to apply
without changing their carriers or functions. This file proves no
existence of a splitting for a nonsplit torus and makes no reduction,
finite-volume or invariant-measure assertion.

The local topology instances have explicit names and expose exactly
`GroupScheme.affinePointsTopologicalSpace` on the actual affine-point
carriers. Their definitions and local scope are unchanged.
