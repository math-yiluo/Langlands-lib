# Proof of the strict blockwise cones for opposite exponents

Authors: Worker 953 (upper cone and final assembly) and Worker 158 (proof
route and the separately published opposite-to-upper reversal adapter).

`Langlands.Exponents.refinedOppositeSquareIntegrableCone` proves exactly the
published closed proposition
`Langlands.Exponents.RefinedOppositeSquareIntegrableConeStatement.{uF,uV}`.
The independent universes `uF` and `uV` and every quantifier of the statement
are kept.

## Proof

After introducing `p`, `F`, `T`, `T.topology`, the rank, the block shape `D`,
the representation `σ : Rep.{uV} ℂ (D.Levi F.Carrier)`, irreducibility, the
analytic hypothesis `hL2 : RelativeRegularComparison.IsLeviSquareIntegrable T D σ`,
the refinement `R`, the character `χ`, the open-kernel and occurrence
hypotheses, and a supplied real part `x`, the proof makes three steps.

1. **One Haar measure.** The proof installs `T.leviTopologicalGroup D` and the
   Borel measurable space `borel` on the actual full central quotient
   `D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)`, with its
   `BorelSpace` instance. The Library theorem
   `PadicField.TopologicalData.exists_isHaarMeasure_leviCentralQuotient` gives a
   Haar measure `μ` there. Specializing the all-Borel-Haar hypothesis gives
   `hL2 μ : IsSquareIntegrableModCenter σ.ρ μ`.
2. **Reversal to the upper quotient.** Worker 158's module
   `Langlands.Representation.Exponents.RefinedOppositeConeReversal` maps the
   actual opposite quotient of `R` injectively to the upper quotient of
   `ProductLeviDualOpposite.reverseRefinement D R`, the refinement with each
   original block's pieces in reverse order. Its theorem
   `isGeneralizedEigencharacter_toUpper` turns the opposite occurrence of `χ` into
   a common-power occurrence of the relabelled character
   `χ.comp (MaximalConeAssembly.precomp (reverseLabel D R).symm)` on the upper
   normalized refined Jacquet module of the reversed refinement. Its theorem
   `isRealPartOf_relabel` turns the supplied real part `x` into the real part
   `x ∘ reverseLabel D R` of that character.
3. **Upper cone and reversal back.** The theorem
   `Langlands.Exponents.RefinedUpperSquareIntegrableCone.isPositiveRootCone`,
   from the companion module
   `Langlands.Representation.Exponents.RefinedUpperSquareIntegrableCone`, applies
   to `μ`, `σ.ρ`, `hL2 μ`, the reversed refinement and the relabelled character
   and real part. It gives, for every original block `j`, the open positive root
   cone for the reversed coordinates of `x ∘ reverseLabel D R`. The adapter's
   `blockwiseCone_neg_of_reverse` reverses each block back and changes the sign,
   giving for every original block `i`

   ```lean
   IsPositiveRootCone
     (fun k : Fin (R i).length => -x (D.flattenBlockEquiv R ⟨i, k⟩))
   ```

   This is the conclusion of the statement: a separate zero sum in each original
   block and strictly negative proper prefix sums of `x`. It includes refinements
   with one piece in a block, where the zero sum forces the coordinate to vanish.

The open-kernel and irreducibility hypotheses are not used: the upper cone
needs neither. The proof uses no tensor presentation, supplied scalar action,
fine-size multiplier, replacement criterion or downstream support or
classification result.

## Where the analytic content lives

The strict prefixes come from
`Langlands.ProductLeviSquareIntegrable.norm_lt_one_of_diagonal`, applied in the
upper module at the prefix test tuples of
`Langlands.ProductLeviNecessity.testScalars`. The separate zero sums come from the
unitary central character in `IsSquareIntegrableModCenter`, evaluated at the
full-block test tuples, which are central in the original Levi. See
`RefinedUpperSquareIntegrableCone.md` for those arguments.

This is an internal derivation from proved Library theorems. It is motivated by
Casselman's strict exponent criterion (Casselman 1995, source
`casselman-1995-admissible-representations`, Theorem 4.4.6, p.45), as recorded in
the statement's Markdown, but does not formalize that theorem.
