# From the special-linear Tits cocycle to the Hermitian presentation

Author: Worker 239.

This internal reduction combines the special-linear cocycle statement with
the constructions of Hermitian coordinates and all-test descent. Its main
theorem is conditional:

```lean
outerTypeAHermitianPresentation_of_specialLinearTitsCocycle
    (hs : SpecialLinearTitsCocycleStatement.{u}) :
    OuterTypeAHermitianPresentationStatement.{u}
```

The proposition `SpecialLinearTitsCocycleStatement` is published, but this
unit assumes a proof of it. Thus this unit does not by itself prove the
unconditional target of Task 6209.

`SpecialLinearTitsCocycle.HasStarMatrixFormulas` records the matrix-valued
star-discrepancy clause of `SpecialLinearTitsCocycleStatement` for a supplied
local presentation, embedding, and family of invertible matrices. It retains
every relative test scheme, cover point, special-linear matrix, and compatible
absolute Galois lift. The two branches use the actual star action: trivial
action gives conjugation, and movement gives conjugation after inverse
transpose. The conversion theorem uses extensionality of invertible matrices
and preservation of inverses by the coefficient map to obtain
`HasStarDiscrepancy`.

The reduction introduces the unchanged hypotheses of
`OuterTypeAHermitianPresentationStatement`, at the same arbitrary universe
and in arbitrary characteristic. Applying `hs` supplies a finite Galois
cover `M/K`, its embedding into the separable closure, a local
special-linear presentation `E`, discrepancy matrices, and the split-torus
characters with their adjacent-root restrictions. The matrix-formula
conversion gives `HasStarDiscrepancy`. The outer star-image hypothesis
forces `n ≥ 2`, and the star-cover containment theorem embeds the actual
field `d.starField` into `M`.

The endpoint hypothesis in the target applies to the vertex numbered zero.
This distinguished first vertex, the root restrictions, and the diagonal
formula meet the hypotheses of
`HasStarDiscrepancy.exists_hermitian_coordinates`. It returns a correction
matrix `P`, a nonsingular Hermitian form `J` over the actual quadratic
star field, trivial discrepancy on that field's image fixer, the
inverse-Gram outer discrepancy for every automorphism moving the field,
and the unchanged diagonal torus coordinates.

The proof installs the embedding of `d.starField` into `M` as an algebra
structure and checks the scalar tower using the embedding's compatibility
with `K`. Pointwise fixation gives membership in the image fixing subgroup,
so the supplied trivial discrepancy implies `InnerTrivial`. Coercing the
outer discrepancy equality from the general linear group to matrices gives
`OuterHermitian`; the outer conjugator is the image of `J.gram⁻¹`.
The theorem `OuterTypeAHermitian.exists_hermitianPresentation` then
supplies the natural all-test matrix homomorphisms, their injectivity,
their exact determinant-one isometry image, and the diagonal split-torus
formula. No restriction to rational points occurs.

For the remaining target clauses, the extension is the actual star field
with its canonical inclusion into the separable closure. Its quadratic
structure comes from the star-image hypothesis and its separability from
being an intermediate field of the separable closure. The established
`fixes_starField_iff` proves precisely the target's pointwise-fixation
equivalence after introducing subfield elements as subtypes. The form's
Hermitian equation supplies the matrix equation, and its invertible Gram
matrix has unit determinant. The original characters and their root
restrictions are retained.

The definitions and proof are internal compositions of the imported
Library interfaces. They assert no new literature result and use no
downstream rank-one classification or Kneser–Tits statement. The assumed
special-linear cocycle theorem remains the sole additional premise of this
conditional reduction.
