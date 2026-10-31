# Determinant multiplication on subgroup-finite and polynomial-growth functions

Author: Worker 2. This is a direct internal construction on the published actual
continuous rational-invariant adelic functions. It uses an arbitrary number field
`F : Type u`, every natural rank including zero, complex coefficients, and the
existing completion and restricted-product topologies.

For any Hecke character, `infiniteOrbitSpan_determinantMultiplier` identifies the
orbit span of the multiplied function under any specified subgroup of the
infinite adelic group with the image of the original orbit span under actual
determinant multiplication. The proof uses the published covariance
`R(g) Mχ = χ(det g) Mχ R(g)`. Each new orbit generator belongs to that image.
Conversely, the character value is a complex unit, so its reciprocal expresses
each multiplied old generator as a scalar multiple of the corresponding new
orbit generator. Neither finite order nor compactness of the subgroup is needed.
Finite dimensionality of a submodule image proves preservation of
`IsInfiniteFinite`; applying the inverse multiplier gives the equivalence.

`InfiniteFiniteRationalFunctions.determinantMultiplier` restricts the actual
continuous complex-linear equivalence to the existing subgroup-finite space.
Preservation in both character directions and the actual inverse law prove
submodule image equality. The forward value is multiplication by `χ(det g)`.
Both the specified infinite subgroup action and the commuting finite adelic
action obey the same character covariance formula.

`HeckeCharacter.HasFiniteOrder.norm_apply` evaluates the positive-exponent
identity defining finite order and applies the complex root-of-unity norm
lemma. Therefore every character value, and hence every adelic determinant
value, has norm one. `norm_evaluate_determinantMultiplier` proves equality of
the original and multiplied function norms at every actual adelic matrix.
Unfolding the existing slice growth predicate gives
`hasPolynomialGrowth_determinantMultiplier_iff` with precisely the same
constant and natural exponent on each fixed finite slice.

`PolynomialGrowthRationalFunctions.finiteOrderDeterminantMultiplier` restricts
the existing continuous linear equivalence using this growth equivalence and
the inverse-character growth equivalence. It retains the inherited subtype
topology from the continuous rational-invariant functions and has the stated
actual evaluation and full right-translation covariance formulas.

The provenance is internal: these are restriction and orbit-span arguments
using `DeterminantMultiplier`, `FiniteVectors`, `Growth`, and
`HeckeCharacterFiniteOrder`, plus the pinned Mathlib complex power/norm and
submodule-image constructions. No new comparison with original literature
is claimed. Smoothness, simultaneous center finiteness, complete automorphic
forms, and total operator-realization twists are separate constructions.
