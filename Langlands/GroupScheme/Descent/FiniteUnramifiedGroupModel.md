# Finite unramified coefficients for smooth affine group schemes

This internal construction applies `FiniteCoefficient.groupModel` and the
published `LocalGalois.Separable.separableUnramified` exhaustion theorem.
`integerCoefficients F E` is the subalgebra of the maximal unramified integers
whose images in the separable closure lie in the intermediate field `E`.
For `E` inside the inertia fixed field it is the integer ring of that field,
viewed as a subring of the maximal unramified integers.

`exists_integerCoefficients` contains any finitely generated coefficient
subalgebra in such a ring for a finite Galois field `E` and records its
arithmetic unramifiedness. The proof chooses generators, applies finite Galois
unramified exhaustion to their field values, and uses the subalgebra generated
by them to extend the containment to all coefficients.

`GroupModel` records the actual group scheme over these coefficients, its
affine and smooth structure morphism, and its base change isomorphism to the
supplied group over the maximal unramified integers. `nonempty_groupModel`
changes the finite coefficient model along the coefficient inclusion;
`groupModel` chooses this construction. Affineness and smoothness are preserved
by base change, and the pullback tower comparison proves recovery.

No semilinear action or Cech descent datum is constructed here.
