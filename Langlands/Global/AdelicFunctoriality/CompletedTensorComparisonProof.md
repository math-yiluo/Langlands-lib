# Canonical completed tensor comparison

`completedTensorComparison` proves exactly the published proposition
`CompletedTensorComparison` in `NormStatement`. It quantifies arbitrary number
fields `K : Type u` and `L : Type v`, with independent universes `u` and `v`,
and their given `Algebra K L`. Its conclusion is bijectivity of the canonical
tensor map at every finite place and every infinite place.

At a finite place `p`, the source is `K_p ⊗[K] L` and the target is the finite
dependent product of the actual adic completions `L_q`, indexed by
`FinitePlacesAbove L p`. This subtype consists of the height-one primes of
`𝓞 L` whose ideals lie over `p.asIdeal`. The map is the existing
`finiteTensorMap` from `Norm`; on a simple tensor its `q` component is
`completionMap p q.1 x * algebraMap L (q.1.adicCompletion L) y`.
The completed algebra comes from continuous extension of the given embedding
of number fields. The infinite conjunct uses `infiniteTensorMap` and the
actual Mathlib infinite places and completions.

The proof introduces the fields and their instances, then proves the two
conjuncts. For a finite prime `p`, it applies the published theorem
`finiteTensorMap_bijective_of_local_degree_bounds` from
`FiniteComparisonReduction`. For each `q : FinitePlacesAbove L p`, the
published theorem `completedLocalDegreeLowerBound K L p q.1` supplies exactly
the required inequality

`e(q/p) * f(q/p) ≤ Module.finrank K_p L_q`.

Here `e` and `f` are the global ramification index and inertia degree of the
actual prime ideals. The lies-over instance is provided by membership in
`FinitePlacesAbove`. No local-degree inequality remains as a hypothesis of
the closing theorem.

The imported finite reduction proves surjectivity by weak approximation for
the inequivalent actual adic absolute values and closedness of the
finite-dimensional image. It computes the source dimension as `[L : K]`
and the target dimension as the sum of the completed local degrees.
Surjectivity gives the upper bound for that sum. Summing the supplied
per-prime inequalities and using the global ramification-inertia sum gives
the reverse bound. The reduction concludes bijectivity by the finite-rank
criterion for a surjective linear map.

The imported `CompletedLocalDegreeProof` proves the arithmetic inequalities
for the actual completed integer rings and their fraction fields. It applies
`Langlands.LocalField.dvrDegreeLowerBound`, rewrites ramification by
`FiniteExtension.completionIntegers_ramificationIdx`, and rewrites inertia by
`FiniteExtension.completionIntegers_inertiaDeg`. The latter comparison uses
the finite residue cardinalities proved in `CompletionResidueAdic` and the
global ideal norm formula. These are proved Library dependencies, so the
assembly assumes neither a decomposition nor a classification of completions.

For the infinite-place conjunct, the proof directly applies
`infiniteTensorMap_bijective` from `Norm`. That theorem combines weak
approximation and closedness of the finite-dimensional image with Mathlib's
infinite local-degree sum. The final module imports the published statement
and all definitions unchanged and introduces no additional hypotheses or
axioms.

This is an internal assembly of published results. Worker 52 wrote the
assembly; the finite reduction incorporates Worker 50's original reduction
and Worker 52's global prime-index and ramification-sum arguments. The
separately published local arithmetic proof is reused by its Lean name.

The original mathematical source is Andre Weil, *Basic Number Theory*,
second edition (1973), Chapter III section 4, Theorem 4, printed pp. 56-57
(PDF pp. 73-74). Registered source: `weil-1973-basic-number-theory`, SHA256
`32fff78f8ccc5d6378907941e26746c34e20fc3adf5096508844cfe8a301e33b`.
These pages were read. The theorem here realizes the field-decomposition
assertion for number fields, with the tensor factors ordered as `K_p ⊗[K] L`
and the finite product represented by a dependent function type. Its proof
uses the dimension and arithmetic arguments above. It does not assert
Weil's additional almost-everywhere statement about integral lattices.
Determinant compatibility, principal norm compatibility, idele-class norm
descent, and reciprocity remain separate results.
