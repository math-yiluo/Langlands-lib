# Finite equations for actual integral actions on abelian schemes

This is an internal specialization of `Langlands.Algebra.FiniteFreeRingHom`.
It imports `Langlands.AbelianScheme.LieOrderBaseChange` and reuses its published
`baseChangeEnd` and `baseChangeOrderAction` constructions. Their additivity
comes from `Langlands.AbelianScheme.RationalBaseChange`. The present
construction uses actual integral endomorphisms throughout.

Let `S` be any scheme in the displayed universe and let `B` be an actual
abelian scheme over it. For any unital ring `O` with a finite integer basis
`b : Basis I ℤ O`, `IntegralActionSolutions b B` consists of tuples
`r : I → CategoryTheory.End B` satisfying the unit and basis-multiplication
equations

\[
\sum_i b.\mathrm{repr}(1)(i)\bullet r_i=1,\qquad
\sum_k b.\mathrm{repr}(b_i b_j)(k)\bullet r_k=r_i r_j .
\]

These equations are equalities in the actual endomorphism ring, including all
possible torsion. Its unit is the actual identity morphism. Its multiplication
convention is `r_i * r_j = r_j ≫ r_i`, so it agrees with ordinary composition
of functions. No commutativity of `O` or of this endomorphism ring is assumed.

`integralActionEquiv b B` is an equivalence from all actual unital ring maps
`O →+* CategoryTheory.End B` to these solutions. It sends an action to its
values on the basis. Its inverse is the integer-linear reconstruction; its
value at every `x` is the sum of the coefficients of `x` times `r_i`, and in
particular its value at `b_i` is `r_i`. The inverse laws are inherited from the
proved generic equivalence.

For every scheme morphism `c : S' ⟶ S`, the published `baseChangeEnd c B` is
the unital ring map induced by the actual pullback functor. Its published laws use functoriality and additivity with the
same endomorphism-ring convention on both sides. There is no flatness or
Noetherian hypothesis.

The published `baseChangeOrderAction` postcomposes an action with this ring map.
`integralActionSolutionsBaseChange` pulls back every tuple entry, retaining the
proved finite equations. `integralActionEquiv_baseChange` and
`integralActionEquiv_symm_baseChange` prove that the equivalence and its inverse
commute with every such actual scheme base change. These are equalities for the
same pulled-back abelian scheme; no identification of independently chosen
integral lifts is asserted.

This construction does not lift a rational algebra action to an integral one.
It does not represent an endomorphism or action functor by a scheme, impose
Rosati conditions, or prove an isogeny or quotient theorem. Ambient polarized
moduli existence, admissibility, smoothness, projectivity, and the normalized
Harris comparison remain separate obligations of the host task.
