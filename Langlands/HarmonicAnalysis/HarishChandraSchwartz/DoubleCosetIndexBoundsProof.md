# Algebraic bounds for finite double-coset indices

The theorem `doubleCosetIndexBounds` proves the complete
`DoubleCosetIndexBoundsStatement` with independent universes for the source
and target groups.

The proof first establishes a triangle inequality for relative indices. Insert
`A ∩ B` between `A` and `C`, use relative-index multiplication in a tower,
and bound the remaining index in `B ∩ C` by the index in `B`. The hypotheses
that the two starting indices are nonzero ensure every use of a finite-index
inequality has its required finiteness proof.

Conjugation preserves relative indices by Mathlib's injective-map formula.
Apply the triangle inequality with `A = ghK(gh)⁻¹`, `B = gKg⁻¹` and `C = K`;
the first factor is the index at `h`, and the second is the index at `g`.
Induction gives the natural-power bound, starting from index one at the identity.

For a homomorphism, the image of `gKg⁻¹` is `f(g) f(K) f(g)⁻¹`.
The comap formula identifies the image relative index with the original relative
index after adjoining the kernel to its first subgroup. Monotonicity in that
subgroup gives both nonzero index and the desired inequality. These are purely
algebraic arguments; no measure, topological finiteness or reductive-group
volume conclusion is assumed or derived here.
