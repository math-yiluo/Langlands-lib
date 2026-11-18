# Reduction of real approximation to connected reductive groups

This module defines two propositions with no universe parameters and proves
nothing. `Langlands.GroupScheme.ReductiveRealApproximationStatement` is the
published real-approximation assertion restricted to connected reductive
group schemes over `ℚ`. It uses the same actual ring points, the same inclusion
`ℚ → ℝ`, and the same evaluation topology as
`Langlands.GroupScheme.RealApproximationStatement`.

`Langlands.GroupScheme.RealApproximationReductiveReductionStatement` says that
this restricted assertion implies the full published assertion for all smooth
connected affine group schemes over `ℚ`. Its conclusion is the unchanged
Library proposition, with no extra hypothesis.

The explicit affine instance in the reductive proposition supplies the point
topology. It is redundant mathematically: `IsConnectedReductive G` already
asserts that the structure morphism is affine.

## Derived provenance

The reduction is the final step of Milne, *Algebraic Groups* (2017), Theorem
25.70, printed p. 564 (registered source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
The characteristic-zero Levi decomposition of §§25.48–25.49 expresses the
group as a semidirect product of a connected reductive group and a smooth
connected unipotent group. Over `ℚ` the latter is split and its underlying
scheme is an affine space by §14.66. Rational affine-space points are dense
in their real points, and density passes through products and the actual
multiplication isomorphism. This module isolates that final reduction as a
separate proposition; it asserts no reductive approximation theorem.
