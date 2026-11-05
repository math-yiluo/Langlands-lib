# Dynamic parabolic coverage from Hermitian right remainders

This internal derived adapter connects the matrix limit argument in
`Langlands.Group.WeightedPolarIwasawa` to actual group scheme points. It uses the
published dynamic subgroup comparison for a closed embedding with diagonal
cocharacter. It introduces no new literature assertion.

Let `k : Type u` be a field, let `G` be a group scheme over `Spec k`, and let
`ρ : G → GL_n` be a matrix representation with finite index type `n : Type`.
The definition `cocharacterPointHom χ A` evaluates an actual cocharacter on
the units of an arbitrary coefficient algebra `A`. It first uses the existing
affine point equivalence for the multiplicative group, then postcomposes with
`χ`. It is a group homomorphism into the actual affine points of `G`.

If `χ ≫ ρ` equals the diagonal cocharacter with integer weights `e`, then
`affineMatrix_cocharacterPointHom` identifies the represented matrix of this
evaluation with `diagonalUnits A e t` for every unit `t`. This follows directly
by functoriality and the existing affine diagonal-cocharacter formula.

If `ρ` is a closed immersion, the theorem
`parabolic_carrier_eq_blockComap` identifies the actual affine
point subgroup of `Dynamic.parabolic χ` with the weighted block comap under
`ρ.affineMatrix`. The existing comparison first gives matrices with entries
in the global sections of the affine test scheme. The canonical algebra
equivalence between these sections and `A` transports membership back to
the original coefficient algebra; the existing block-subgroup invariance
under ring equivalence supplies the last step. No topological assumptions
on `A` are needed for this identification.

Now let `A : Type u` be an `RCLike` field and a `k`-algebra. Equip the actual
affine points with their existing regular-function evaluation topology.
The theorem `parabolic_mul_compact_eq_univ_of_hermitian` assumes a compact
subgroup `K` and, for every point `x`, a point `z ∈ K` such that the represented
matrix of `x * z⁻¹` is Hermitian. It proves the literal ordered product
`Dynamic.parabolic χ(A) * K = Set.univ`.

The proof evaluates `χ` at the units given by the nonzero real parameters
`t_m = (1/2)^m` in `A`. The resulting points have matrices
`diag((t_m : A) ^ e_i)`. The representation on affine points is continuous
by the existing continuity of postcomposition and of the affine matrix
equivalence. The weighted covering theorem therefore applies, and the
subgroup identification gives the result. There is no independently supplied
diagonal sequence in this theorem's hypotheses.

Finally, `range_mul_compact_eq_univ_of_hermitian` takes an actual group scheme
morphism `p : P → G` representing `Dynamic.parabolic χ`. Its range on actual
affine points is the carrier of that subgroup functor by the representing
property. Substitution gives the literal point-map range times `K`, in the
same order as the actual Iwasawa target.

These results retain the closed representation, compatible diagonal
cocharacter, compact subgroup and Hermitian remainder hypotheses. They do not
construct a self-adjoint realization or a maximal compact subgroup, and do not
infer that an arbitrary geometric parabolic is represented by this dynamic
subgroup. Those remain obligations for the full archimedean Iwasawa existence
theorem. The coefficient algebra and base field retain the original universe
`u`; no reduction to a particular small scalar field is made.
