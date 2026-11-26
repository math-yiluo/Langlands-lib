# Induction from a witnessed unitary supercuspidal support

`Langlands.VirtualRepresentation.PadicSupercuspidal.exists_equiv_unitarizableSupercuspidalProduct` realizes a positive-rank representation with a witnessed unitary supercuspidal support as the normalized induction of unitarizable supercuspidal blocks. The representation carrier and the local field lie in the same universe, as in the automorphic support of a witnessed generator.

The proof opens `IsUnitaryLatticeSupport` to obtain a list of inducing classes and an irreducible subquotient of the corresponding induction. Each class belongs to the given multiset of unitary data, so each chosen representative is unitarizable. `Classification.unitarizableSupercuspidal_isSquareIntegrable` gives square integrability, and `Classification.squareIntegrableBlockInduction` makes the normalized induction irreducible. `CuspidalInductionConstituent.nonempty_equiv_of_isSubquotient` identifies the irreducible subquotient with the full induction.

This local consequence of unitary support and square-integrable block induction applies to the automorphic components of witnessed generators in `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
