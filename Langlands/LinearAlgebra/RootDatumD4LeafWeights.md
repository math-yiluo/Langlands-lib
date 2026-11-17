# Fundamental leaf weights of a numbered D4 root datum

This is an internal lattice computation for the remaining D4 case of the local
rank-one index problem. It uses the Library's integral fundamental weights and
Mathlib's actual Cartan matrix, without any hypothesis on a ground field.

Let `P` be an integral root datum, `b` a base, and assume that the coroots span the
whole coweight lattice over the integers. The existing
`Langlands.RootDatum.fundamentalWeightBasis` then gives integral fundamental
weights dual to the simple coroot basis. Let `e` number the simple vertices by
`Fin 4`, preserving every Cartan pairing and the matrix `CartanMatrix.D 4`.
The central vertex is numbered `1` and the leaves are `0`, `2`, and `3`.

The definition `d4LeafWeightSum` is the sum of the three fundamental leaf weights.
Writing the numbered simple roots as `αᵢ` and their fundamental weights as `ωᵢ`,
the theorem `d4LeafWeightSum_eq` proves

`ω₀ + ω₂ + ω₃ = 2α₀ + 3α₁ + 2α₂ + 2α₃`.

The proof pairs both sides with each simple coroot. The existing separation
theorem for these pairings reduces equality to four computations with the
displayed Cartan matrix. The coroot values of both sides are `(1, 0, 1, 1)`.
The theorem `d4LeafWeightSum_mem_rootSpan` records membership in the integral
root lattice. The theorem `d4LeafWeight_classes_sum_eq_zero` states the resulting
zero-sum relation among the three weight classes in the actual quotient
`X / P.rootSpan ℤ`. Its proof uses the kernel criterion for the quotient map.

These are derived algebraic computations from the imported definitions. No
separate literature theorem is needed for them. They do not construct Tits
algebras, identify this quotient with the character group of a group-scheme
centre, prove a corestriction formula, or exclude a local D4 index.
