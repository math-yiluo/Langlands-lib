# Place-level glue for the local modular-character formula

Author: Worker 1402.

This helper module supplies two small facts used in the proof of
`Langlands.Global.PlaceGroupPoints.LocalModularCharacterAdjointDeterminantStatement`.

- **(A)** The completion `w.Completion` of a field at an infinite place `w`, with its
  existing normed-field structure, admits a real normed-space structure for which it is
  finite-dimensional over `ℝ`.
- **(B)** At a place `i` of a number field `F`, with `K = placeCompletion F i`, a
  `K`-linear automorphism `A` of `Fin d → K` whose determinant equals that of the adjoint
  action `Ad(g)` of `g ∈ G(K)` has additive Haar character equal to the local norm of the
  adjoint determinant character `det Ad` at `g`.

## Provenance

This module is internal glue. It adds no definitions and no new mathematics. Part (A)
uses Mathlib's identification of an archimedean completion with `ℝ` or `ℂ`, through the
isometric ring isomorphisms `NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal` and
`NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex`. It transports the real
scalars of `ℝ` or `ℂ` along them. Part (B) combines two earlier results:

- the Haar scaling lemma `addEquivAddHaarChar_placeLinear_eq_placeNorm` from
  `Langlands.Global.LocalModularCharacter.HaarScaleNorm`, which is Weil, *Basic Number
  Theory*, Ch. I, §2, Corollary 3 of Theorem 3 (`mod_V(A) = mod_K(det A)`);
- the Library identification `Langlands.GroupScheme.Lie.adjointDeterminantCharacter_val`
  of the rational character `det Ad` with `LinearMap.det` of the actual adjoint
  endomorphism. That character implements Getz–Hahn, *An Introduction to Automorphic
  Representations* (2024), §3.6, equation (3.13).

## Declarations

All declarations are in namespace `Langlands.Global`.

- `exists_normedSpace_real_of_ringEquiv e he`: let `E` and `V` be normed fields, with `V`
  a finite-dimensional real normed algebra. Let `e : E ≃+* V` be a ring isomorphism with
  `‖e x‖ = ‖x‖` for all `x`. Then `∃ _ : NormedSpace ℝ E, FiniteDimensional ℝ E`, where the
  normed-space structure is over the given norm of `E`.
- `exists_normedSpace_real_infiniteCompletion w`: for any field `F : Type u` (no
  number-field hypothesis is needed) and any `w : InfinitePlace F`,
  `∃ _ : NormedSpace ℝ w.Completion, FiniteDimensional ℝ w.Completion`, for the existing
  normed-field structure on `w.Completion`.
- `addEquivAddHaarChar_placeLinear_eq_localCharacterNorm F G i g A hA`: let `F : Type u` be
  a number field and `G` a group scheme over `Spec F` with affine total space and locally
  finite type structure morphism. Let `i : Place F`, `g : PlaceGroupPoints F G i` and
  `K = placeCompletion F i`. Let `Fin d → K` carry any Borel measurable structure, and let
  `A : (Fin d → K) ≃ₗ[K] (Fin d → K)` satisfy
  `hA : LinearMap.det A = LinearMap.det (Langlands.GroupScheme.adjoint G K g)`. Then

  `addEquivAddHaarChar (placeLinearContinuousAddEquiv F i A) =
    (AdelicGroupPoints.localCharacterNorm F G (Lie.adjointDeterminantCharacter G).toMul i g : ℝ≥0)`.

  The adjoint endomorphism is `Langlands.GroupScheme.adjoint`, the actual action of `g` on
  the Lie kernel over `K`. The determinant hypothesis makes no claim about how `A`
  relates to `Ad(g)` beyond equal determinants.

## Implemented proof

**General transport.** In `exists_normedSpace_real_of_ringEquiv`, the proof sets the
`ℝ`-algebra structure on `E` to the ring homomorphism `e.symm ∘ algebraMap ℝ V`. Then
`e (r • x) = r • e x`, by `Algebra.smul_def` and `e (e.symm y) = y`. The normed-space
inequality `‖r • x‖ ≤ ‖r‖ ‖x‖` follows by rewriting `‖r • x‖ = ‖e (r • x)‖ = ‖r • e x‖`,
then applying `norm_smul` in `V` and `he` again. The map `e` is therefore an `ℝ`-linear
equivalence `E ≃ₗ[ℝ] V`, and `LinearEquiv.finiteDimensional` transfers finite
dimensionality from `V`.

**Infinite completions.** `exists_normedSpace_real_infiniteCompletion` splits on
`w.isReal_or_isComplex`.

- At a real place it applies the general lemma to `ringEquivRealOfIsReal hw`, with
  `V = ℝ`. That map is `extensionEmbeddingOfIsReal hw`, which is an isometry
  (`isometry_extensionEmbeddingOfIsReal`), and an isometry that fixes `0` preserves norms.
- At a complex place it applies the general lemma to `ringEquivComplexOfIsComplex hw`,
  with `V = ℂ`. That map is `extensionEmbedding w`, which is an isometry
  (`isometry_extensionEmbedding`).

**Determinant glue.** In `addEquivAddHaarChar_placeLinear_eq_localCharacterNorm`, the
proof first rewrites the left side with `addEquivAddHaarChar_placeLinear_eq_placeNorm` to
`placeNorm F i (LinearEquiv.det A)`. By the definition of `localCharacterNorm` (the
composite of `placeNorm F i` with `characterUnits`), the right side is definitionally
`placeNorm F i (characterUnits F G (adjointDeterminantCharacter G).toMul K g)`. It then
remains to show that the two units are equal, which `Units.ext` reduces to their values.
`LinearEquiv.coe_det` and `hA` turn the left value into
`LinearMap.det (adjoint G K g)`. The Library theorem `adjointDeterminantCharacter_val`
says that this determinant is the value of the unit obtained by evaluating `det Ad` at
`g` through `Gm.affinePointsEquiv`. That unit is `characterUnits` with its definition
unfolded, so the symmetric form of this theorem closes the goal.

Both main theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
