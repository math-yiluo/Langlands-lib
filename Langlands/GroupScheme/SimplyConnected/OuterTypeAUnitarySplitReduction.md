# Outer type A presentations from the Tits cocycle and unitary splitting

This internal module proves that the published proposition
`SpecialLinearTitsCocycleStatement` implies the published proposition
`OuterTypeAUnitarySplitPresentationStatement`, in the same universe. The Tits
cocycle proposition remains an explicit premise. This unit does not prove the
unconditional target.

## Discrepancy conversions

The first clause of `SpecialLinearTitsCocycleStatement` states the Galois
discrepancy formulas as equalities of matrices over the global sections of a test
scheme. The infrastructure predicates `HasInnerDiscrepancy` and
`HasOuterDiscrepancy` state the same formulas in the general linear group. Two
Prop-valued definitions name the matrix forms. Here `E` is a local isomorphism from
`SL_(n+1)` to `G` over `Spec M`, `σ : M ≃ₐ[K] M` and `X ∈ GL_(n+1)(M)`.

- `IsInnerMatrixFormula E σ X` (def): for every test `Z` over `Spec K`, every cover
  point `a : Z ⟶ cover K M` and every `g ∈ SL_(n+1)(Γ(Z))`, the matrix of
  `discrepancy E σ a g` equals `X_a g X_a⁻¹`. Here `X_a` is the image of `X` under
  `coefficients a`, and `X_a⁻¹` is the image of `X⁻¹`.
- `IsOuterMatrixFormula E σ X` (def): the same, with `X_a (g⁻¹)ᵀ X_a⁻¹` on the
  right-hand side.

These are exactly the two implications of clause 1 of
`SpecialLinearTitsCocycleStatement` for the matrix `x σ`. The three lemmas below
translate between the two forms. Each one applies `Units.ext` or
`congrArg Units.val` and rewrites the image of an inverse with `map_inv`.

- `hasInnerDiscrepancy_of_matrix`: `IsInnerMatrixFormula E σ X` gives
  `HasInnerDiscrepancy E σ X`.
- `hasOuterDiscrepancy_of_matrix`: `IsOuterMatrixFormula E σ X` gives
  `HasOuterDiscrepancy E σ X`.
- `isOuterMatrixFormula_of_hasOuterDiscrepancy`: the converse of the outer
  conversion. It supplies the matrix formula that
  `OuterTypeAHermitian.OuterHermitian` uses.

## The reduction

`outerTypeAUnitarySplitPresentation_of_specialLinearTitsCocycle` assumes
`SpecialLinearTitsCocycleStatement.{u}` and proves
`OuterTypeAUnitarySplitPresentationStatement.{u}`. Fix `K` with
`UnitaryInvolutionSplitting K`, a group `G` with Tits index data `d`, a type-A
numbering `e`, and a Galois element `σ₀` whose star action moves a vertex. The
proof runs as follows.

1. Since the star action is not trivial, `starImagePair_of_A` shows that its
   image under `e` is the identity and the chain reversal. Hence `2 ≤ n`, and the
   actual star field `d.starField` is a separable quadratic Galois extension of
   `K` (`StarImagePair.isQuadraticExtension`, `StarImagePair.isGalois` and the
   instance `isSeparable_starField`).
2. The cocycle premise gives a finite Galois extension `M/K` with an embedding
   `ι₀` into the separable closure, a local isomorphism `E` from `SL_(n+1)` to `G`
   over `Spec M`, and matrices `x σ`. The torus and root clauses are discarded.
   The conversions above turn the first clause into `HasStarDiscrepancy E d ι₀ x`.
3. `HasStarDiscrepancy.starField_le_cover` places the star field inside the image
   of `ι₀`. This gives the embedding `f = starFieldToCover d ι₀ hle` and the
   intermediate field `F = f.fieldRange`, which is quadratic over `K`. Let `H` be
   its fixing subgroup, which has index two. An automorphism of `M` lies in `H`
   exactly when it fixes every `f z`. So `HasStarDiscrepancy.inner_of_fixes_starField`
   gives inner representatives `x σ` on `H`, and
   `HasStarDiscrepancy.outer_of_not_fixes_starField` gives outer representatives
   off `H`.
4. `isTwistedProjectiveCocycle_of_discrepancy` turns these representatives into
   the twisted projective cocycle law for `x` relative to `H`. With the splitting
   hypothesis, `UnitaryTwistedDescent.exists_conj_eq_scalar` gives `P` such that
   `P⁻¹ x(σ) σ(P)` is a scalar for every `σ ∈ H`. Then
   `hasTrivialDiscrepancy_coordinateChange_of_scalar` shows that the coordinate
   change `E' = coordinateChange E P` has trivial discrepancy on `H`.
5. `exists_starFieldToCover_conjugation` gives an automorphism `σ` of `M` that
   restricts to the quadratic conjugation on the star field. Then `σ` moves the
   star field, and the coordinate change of its outer representative is an outer
   representative for `E'`. `exists_hermitian_outer_representative` gives a
   nonsingular Hermitian matrix `J` over the star field, for its nontrivial
   automorphism. The image of `J⁻¹` is then an outer representative for `E'` at
   every automorphism that acts on the star field by conjugation. By
   `starFieldToCover_conjugation_of_not_fixed`, these are exactly the
   automorphisms that move the star field. This step repeats the second half of
   the proof of `HasStarDiscrepancy.exists_hermitian_coordinates`, with the
   coordinate change from step 4 replacing the inner correction, which needs a
   distinguished endpoint.
6. Make `M` a star-field algebra through `f`. The two facts above are exactly
   `OuterTypeAHermitian.InnerTrivial` and `OuterTypeAHermitian.OuterHermitian`
   for `E'` and `J`. So `OuterTypeAHermitian.descendedIso` gives an isomorphism
   `φ` from the special unitary group scheme of `J` to `G`.
7. The required presentation is
   `HermitianMatrix.SchemeModel.Presentation.ofMatrixPoints`, applied to the
   matrix points of `G` through `φ`. Injectivity, the exact Gram-and-determinant
   image and naturality are `OuterTypeAHermitian.matrixPoints_injective`,
   `mem_range_matrixPoints` and `matrixPoints_naturality`.

The witness field in the target is `L = d.starField`, the field of definition of
the actual star action, with its separable quadratic structure over `K`. The
Hermitian form is `J`, of size `n + 1`.

## Provenance

This is internal infrastructure. It does not formalize a statement from the
literature. Its route is the classical one. Over the star field, the cocycle of an
outer type-A form defines a central simple algebra with a unitary involution. When
that algebra splits, a coboundary makes the inner part trivial. The outer part is
then a Hermitian form, so the group is `SU(J)`. For the classical statement that
absolutely simple simply connected groups of type `A_n` are the groups `SU(B, τ)`,
see Knus–Merkurjev–Rost–Tignol, *The Book of Involutions* (1998), §26.A,
Theorem (26.9) (printed p. 366, PDF p. 389). The Lean proof composes the Library
and infrastructure results named above.
