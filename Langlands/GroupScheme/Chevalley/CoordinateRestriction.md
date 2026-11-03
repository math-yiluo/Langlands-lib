# Coordinate restriction and all scheme tests

This internal bridge relates the coordinate ideal criterion to the actual
group-scheme range functor. It uses the coordinate bialgebras and all-test
point comparisons in the published `AffineLinearEmbedding.Coordinate` and
`CorepresentedPoints` modules.

For two corepresented group functors and a natural group homomorphism
`α : H → F`, `coordinateRestriction` is the algebra map classifying the
image of the universal point of `H`. Naturality identifies composition with
this algebra map with the homomorphism on every algebra point. Preservation
of the identity and multiplication then proves compatibility with the
counit and comultiplication, giving `coordinateRestrictionBialgHom`.

`factors_coordinateRestriction_iff` identifies factoring algebra maps with
points in the image of `α`. The theorem
`mem_range_iff_coordinate_factors` transports this equivalence through the
relative Spec/global-sections adjunction. Its left side uses exactly
`SubgroupFunctor.range` for the actual induced group-scheme map. The
equivalence holds for every relative scheme `T`; it assumes neither
affineness nor reducedness of `T`.

Closedness of the actual induced group-scheme map implies surjectivity of
coordinate restriction: global sections of an affine closed immersion are
surjective, and the canonical section isomorphisms for affine spectra
identify this homomorphism with coordinate restriction.

Over a field, finite type of the ambient coordinate algebra makes it
Noetherian, so the restriction kernel is finitely generated. The final
theorem `exists_finite_subspace_range_criterion` combines these facts with
`IdealCriterion`. It constructs one finite-dimensional regular subspace
whose ideal-intersection criterion detects the actual range on every
relative scheme test. A projective stabilizer and homogeneous scheme
quotient remain later constructions.
