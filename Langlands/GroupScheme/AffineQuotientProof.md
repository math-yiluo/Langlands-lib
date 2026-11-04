# Affineness of a represented fpqc quotient

`Langlands.GroupScheme.affineGroupSchemeQuotient.{u}` proves exactly
`Langlands.GroupScheme.AffineGroupSchemeQuotientStatement.{u}`.
For any field `k : Type u`, let `G` and `Q` be actual group schemes over
`Spec k`, with `G` affine and locally of finite type, and `Q` separated,
locally of finite type and quasi-compact. If the scheme map of an actual
homomorphism `q : G ⟶ Q` is flat, surjective and quasi-compact, then `Q`
is affine over `k`.

The proof applies the reduction in `AffineQuotientReduction` to the theorem
`AffineQuotient.smoothNormalKernel` in
`MatrixRepresentation/SmoothNormalKernel`. There is no remaining
theorem-valued premise.

First, over an algebraically closed field, a closed normal subgroup of a
smooth affine algebraic group is the exact scheme-theoretic kernel of a
finite matrix representation. The construction uses a Chevalley line whose
stabilizer is the subgroup, split coordinates selected from its rational
orbit, and normality to make the subgroup action diagonal in those
coordinates. Tensoring the original representation with the dual of the
orbit representation cancels the subgroup's unit scalar on a distinguished
tensor vector. That vector's stabilizer lies in the subgroup. The
representation on the whole subgroup-fixed subspace therefore has exactly
the prescribed kernel. These comparisons hold on every relative scheme
test, so the subgroup may be nonreduced.

For a smooth source over an algebraically closed field, apply that
construction to the kernel of `q`. The schematic image of the resulting
representation is affine and smooth. The dominant image projection is
flat, surjective and quasi-compact. Equality of its kernel with the kernel
of `q` allows fpqc descent of homomorphisms in both directions. Uniqueness
of descent makes the descended maps inverse, identifying `Q` with that
affine image.

For an arbitrary source over an algebraically closed field, pass to the
reduced subgroup schemes of `G` and `Q`. They are smooth, the reduced source
is affine, and the induced homomorphism is scheme-surjective. The published
dominant-flatness theorem makes it flat and quasi-compact, so the smooth
case applies. The reduced subscheme of `Q` is consequently affine. Its
finite surjective closed immersion into `Q`, together with finite-surjective
affine descent, proves that `Q` is affine.

Finally, base change from the original field to its algebraic closure.
The required structure-map properties and scheme-surjectivity are
preserved. The algebraically closed case proves that the base change of
`Q` is affine; field-extension affine descent gives affineness of `Q`.
Thus no smoothness, connectedness, perfectness or characteristic
restriction is imposed on the original data. Surjectivity throughout is
surjectivity of scheme maps.

The source theorem is Milne, *Algebraic Groups* (2017), Proposition 5.18
and the quotient universal property of Theorem 5.13, with Proposition 5.29
giving the represented normal-quotient formulation. The implemented route
uses algebraic closure and reduced subgroups instead of Milne's finite
extension and Weil-restriction step. The normal-kernel construction follows
the orbit, dual and fixed-space argument of Lemmas 5.16–5.17. The source and
errata correspondence for the target are recorded in the unchanged
`AffineQuotientStatement` pair.

Worker 706 supplied the rational-orbit and eigenline constructions and
assembled the normal-kernel and final proofs. Worker 239 supplied the
dual/tensor calculations and the arbitrary-field quotient reduction.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
