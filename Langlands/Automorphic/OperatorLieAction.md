# Lie actions on actual automorphic realizations

This internal construction applies to a number field `F`, every natural rank `n`, and an actual `OperatorRealization F n` named `S`. Its space remains the concrete subspace `S.Space` of stable automorphic functions.

`complexLieAction` composes the published genuine enveloping algebra action `S.envelopingAction` with the canonical generator map of `ArchimedeanGL.ComplexLieAlgebra F n`. The result is a complex-linear Lie homomorphism to the endomorphisms of the same space. The accompanying `complexLieRingModule` and `complexLieModule` instances are the pullback of the usual evaluation action of endomorphisms. Thus the bracket with a vector is precisely the existing differential operator applied to the vector, as expressed by `complex_lie_eq` and `inclusion_complexLieAction`.

`compactLieAction` restricts along the published `compactComplexInclusion`, obtained by complexifying the inclusion of skew-adjoint archimedean matrices. Its Lie module instances pull back the complex Lie module along that same inclusion. `compact_lie_eq` identifies the bracket with this explicit restricted action. These constructions reuse the concrete compact Lie algebra, rather than choosing another subalgebra.

`finiteRepresentation_complexLieAction` records commutation with the existing finite adelic translations. It specializes the published commutation of finite translations with the enveloping algebra action to a generator.

Both `Intertwiner.complexLieRestriction` and `Intertwiner.compactLieRestriction` are bundled Lie module maps with the same underlying linear map as the full operator intertwiner. Their proofs specialize `Intertwiner.differential` to the respective enveloping generator. The two corresponding `Equivalence` constructions retain the original inverse linear map. The application lemmas make explicit that no vectors or maps have changed.

The provenance is internal composition of `OperatorRealization`, `OperatorEquivalence`, `ArchimedeanLieAlgebra`, and `ArchimedeanCompactLieAlgebra`, using Mathlib's `AlgHom.toLieHom`, endomorphism evaluation action, and `LieRingModule.compLieHom` / `LieModule.compLieHom`. This module does not yet construct relative cochains, cohomology, algebraic coefficient representations, or the split-center quotient required for the cohomological infinity condition. It also does not identify this compact Lie action with differentiation of the compact group representation; that analytic compatibility is a separate obligation.
