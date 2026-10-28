# A closed coefficient component in the actual central L2 completion

Authors: Worker 386 and Worker 801.

This module proves
`Langlands.squareIntegrableCoefficientHilbertComponent :
SquareIntegrableCoefficientHilbertComponentStatement.{uG,uV}` with no
extra hypotheses. The group and carrier universes stay independent. The
algebraic carrier `V` gets no topology and no finite-dimensionality
assumption. The proof is internal derived infrastructure: it applies
published Library results and does not transcribe a numbered theorem
from the literature.

## Construction

Fix a group `G` with the compact-open cofinality condition, an
algebraically irreducible `ρ` on `V`, a Borel Haar measure `μ` on
`G ⧸ center G` that is right invariant, a proof
`hsq : IsSquareIntegrableModCenter ρ μ`, and a proof of `IsUnitarizable ρ`.

1. The published
   `IsSquareIntegrableModCenter.exists_coefficientL2_embedding` gives a
   unitary central character `c`, a smooth-dual functional `ℓ` with
   `ℓ.val ≠ 0`, and square integrability `hL2` of every coefficient norm.
   These are the statement's `c` and `ℓ`. The injectivity clause it also
   returns is not used.
2. `j` is `c.coefficientL2Intertwiner hsq.1.1 ℓ.val μ hL2`, the actual
   coefficient map into `Induction.centralL2Representation`. Its value
   in central induction is `c.coefficientIntertwiner hsq.1.1 ℓ.val v` by
   definition.
3. `b` is `c.coefficientL2Form hsq.1.1 ℓ.val μ hL2 hℓ`. This is the comap
   of `Induction.centralL2Form` along `j`, so the equation
   `b.inner v w = B.inner (j v) (j w)` holds by `rfl`. The same `rfl` is
   the form-preservation input `hf` of the completion construction.
4. `e` is the published `InvariantPositiveForm.completedIsometry B j hf`,
   which extends `j` to a linear isometry
   `b.HilbertCompletion →ₗᵢ[ℂ] B.HilbertCompletion`. The extension
   property is `completedIsometry_toHilbert`, and equivariance for the
   completed representations is
   `completedIsometry_completedRepresentation`.
5. `R` is the published `completedRange B j hf`, the range of `e` as an
   invariant subspace of the completed representation. The range
   equation is `coe_completedRange`, and closedness is
   `isClosed_completedRange` (the image of a complete space under an
   isometry is closed).

## The remaining clauses

* Continuity of each completed orbit `g ↦ B.completedRepresentation g y`
  is the published `continuous_completedOrbit`, applied to smoothness of
  the central L2 representation (`Induction.centralL2Representation_smooth`).
* Closed irreducibility of `b.HilbertCompletion`:
  `CoefficientHilbertComponentAux.completion_closed_irreducible` applies the
  proved `admissibleAlgebraicToClosedIrreducibility` to the canonical
  completion. The admissibility input is `hsq.1`. The dense map is
  `b.toHilbert`, the operators `b.completedLinearMap` are packaged as a
  monoid homomorphism, and the inner-product identity is `inner_toHilbert`.
  The result `IsTopologicallyIrreducible` is then restated for
  subrepresentations through `Subrepresentation.toSubmodule_injective`.
* `CoefficientHilbertComponentAux.closed_irreducible_range` transfers this
  to `R`. Restricting the codomain of `e` to `R` gives a continuous linear
  bijection `q`. The preimage under `q` of a closed invariant subspace of
  `R` is closed and invariant in the source, so it is bottom or top.
  Surjectivity of `q` carries that alternative back to `R`, and
  injectivity carries nontriviality. This lemma needs no group topology.
* Smooth-vector recovery in `b.HilbertCompletion`:
  `CoefficientHilbertComponentAux.completion_smooth_recovery` applies the
  proved `admissibleSmoothVectorRecovery` to `toHilbertIntertwiner b`,
  which is `b.toHilbert` regarded as an intertwiner into
  `b.completedRepresentation`. It also uses continuity of each
  `b.completedOperator g`, density, and `inner_toHilbert`.
* `CoefficientHilbertComponentAux.smooth_range_image` transfers recovery
  to the ambient completion. A vector `e x` has an open stabilizer exactly
  when `x` does, by `isSmoothVector_map` and `isSmoothVector_of_injective`.
  With the range equation, a vector `y` lies in `R` and is smooth exactly
  when `y = e (b.toHilbert v)` for some `v : V`.

## Provenance

Worker 386 wrote the two transfer lemmas and the two applications to the
completion. In that draft the irreducibility application still took the
comparison statement as an explicit input. Worker 801 replaced that input
with the published proof `admissibleAlgebraicToClosedIrreducibility`,
added `toHilbertIntertwiner`, and assembled the final theorem from the
published coefficient, central L2, completion and completed-intertwiner
APIs.
