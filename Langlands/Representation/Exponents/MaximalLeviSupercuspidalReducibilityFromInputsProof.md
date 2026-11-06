# Proof of Renard VII.1.3 from its remaining inputs

Lean module: `Langlands.Representation.Exponents.MaximalLeviSupercuspidalReducibilityFromInputsProof`.

Theorem `maximalLeviSupercuspidalReducibilityFromInputs :
MaximalLeviSupercuspidalReducibilityFromInputsStatement.{u, v}`.

The published statement says that `MaximalLeviSupercuspidalReducibilityStatement.{u, v}`
(Renard VII.1.3) follows from eleven published propositions. See
`MaximalLeviSupercuspidalReducibilityFromInputsStatement.md`. The proof here only
assembles theorems proved in other modules of this contribution:

1. **Twist reduction.** `maximalLeviSupercuspidalReducibility_of_unitary` (module
   `MaximalLeviTwistReduction`, by Worker 1517) derives the target from two statements:
   - its unitary case `MaximalLeviSupercuspidalReducibilityUnitaryStatement`, in which
     `i_P^G ρ` also has a unitary central character;
   - the twist statement `MaximalLeviUnitaryCentralTwistStatement`.

   This is the first paragraph of Renard's proof: twist by an unramified character of
   `G`, then apply the Mackey isomorphism.
2. **Twist statement.** `maximalLeviUnitaryCentralTwist_of_parabolicDynamic` (module
   `MaximalLeviUnitaryCentralTwistReduction`, by Worker 1517) proves the twist statement
   from `ParabolicDynamicStatement`, the first premise.
3. **Unitary case.** `maximalLeviSupercuspidalReducibilityUnitary_of_inputs` (module
   `MaximalLeviReducibilityUnitaryProof`) proves the unitary case from ten input
   statements. Six of them are premises here:
   - irreducible implies admissible, at carriers `v` and `max u v`;
   - I1;
   - K1, K2 and C.

   The other four are proved:
   - `leviInductionAdmissible_of_quotientCompact` gives admissibility of induction from
     quotient compactness;
   - `leviInductionUnitarizable_of_inputs` gives unitarizability of induction from
     unimodularity, standard cocharacters, quotient compactness and root presentations;
   - `leviInductionNontrivial` gives nonzeroness of induction, with no hypotheses;
   - `leviInductionHermitianDuality_of_presentation` (module
     `LeviInductionHermitianDualityReduction`, by Worker 1517) gives hermitian duality of
     induction from the same four premises as unitarizability.

   The first three are in module `MaximalLeviReducibilityInductionInputs`.

The Lean proof introduces the eleven premises and applies these theorems in this order.
It uses no other argument.
