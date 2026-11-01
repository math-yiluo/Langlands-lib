# Actual determinant twists of half-twisted adelic sections

Author: Worker 2. Provenance: internal construction from the actual adelic
section spaces, block Hecke characters and determinant multipliers. There is no
new identification with original literature or Haar normalization.

The number field has arbitrary universe `uF`. All natural ranks and positive
ordered block shapes, including the empty shape at rank zero, are retained.
The coefficient space has independent universe `uV`.

`determinantTwist` twists an actual complex Levi representation by the actual
block character with the same Hecke character on every block. The published
determinant formula for an actual parabolic matrix identifies this block
character with the ambient determinant character.
`inducingRepresentation_determinantTwist` proves that the constructed positive
half commutes with this scalar twist.

`sectionDeterminantEquiv` is actual pointwise multiplication
`f(x) ↦ χ(det x) • f(x)` on covariant functions. Its inverse is multiplication
by the inverse unit. Both covariance laws, inverse identities and complex
linearity are proved directly on actual values. The evaluation formulas expose
these functions. `sectionDeterminantTwistEquiv` proves that this map intertwines
the ambient determinant twist of actual right translation with induction from
the twisted Levi coefficients.

This algebraic construction uses arbitrary complex coefficient modules and
arbitrary continuous Hecke characters.

The regularity restrictions require `χ.HasFiniteOrder`.
`finiteSmooth_of_determinant_multiply` retains an actual common open finite
stabilizer by intersecting the old one with `χ.finiteDeterminantKernel`.
The determinant factor is one on the second subgroup, so pointwise evaluation
of the old invariance identity proves invariance of the product.
The forward and inverse multiplication maps preserve finite smoothness;
the inverse uses the finite-order character `χ⁻¹`.
`finiteSmoothDeterminantEquiv` is the resulting complex linear equivalence.
Its forward and inverse evaluation formulas are exactly the actual
multiplication functions. `finiteSmoothDeterminantTwistEquiv` restricts the
algebraic intertwining law to the two finite-smooth section spaces.

For arbitrary complex normed coefficient spaces,
`infiniteSmooth_of_determinant_multiply` proves preservation of every
real-smooth archimedean slice. The finite-order determinant character is
locally constant on the full adelic group. Pulling this function back along
the actual mixed archimedean coordinates, with the finite matrix fixed,
makes it constant near each point. The multiplied vector-valued slice is
therefore locally equal to a constant complex scalar multiple of the old
smooth slice. Smoothness is local, so it follows at each point. Applying
this argument to `χ` and `χ⁻¹`, and combining it with the two finite
stabilizer arguments, constructs `smoothDeterminantEquiv` on the actual
`SmoothSections`. Its forward and inverse evaluation identities expose
the same multipliers as before.

`smoothDeterminantTwistEquiv` proves the resulting equivalence of actual
full adelic representations. It restricts the proved algebraic intertwining
identity; it does not infer archimedean smoothness from a whole-group open
stabilizer. The section spaces here have no newly assigned function-space
topology, and no continuity of the section equivalence in a derivative or
compact-open topology is claimed.

No completeness, finite-dimensionality or continuity of the Levi
representation is assumed. This construction does not assert nonzero
sections, automorphic occurrence, unitary completion, Haar identification
or isobaric classification.
