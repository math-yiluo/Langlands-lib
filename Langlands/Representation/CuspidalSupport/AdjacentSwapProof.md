# Adjacent block swaps preserve the factors of cuspidal induction

Author: Worker 289.

`Langlands.CuspidalSupport.adjacentBlockSwapCuspidalInductionFactorsTheorem`
proves the published
`AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW}`. The field
universe and the two inducing carrier universes are independent. The theorem
has the exact target type and introduces no additional hypotheses.

For every prime, actual finite p-adic extension, compatible topological data
and positive rank, the target takes two ordered block shapes and a minimal
coordinate permutation conjugating their whole Levis. The permutation sends
block `i` to block `swap j (j + 1) i`, where `j + 1` is below the number of
source blocks. Given irreducible smooth Levi-cuspidal representations and an
actual equivalence between the transported source representation and the
target representation, it supplies matching Jordan–Hölder factors for their
canonical normalized inductions. The conclusion includes actual finite
composition series and a permutation matching their irreducible quotient
representations by actual equivalences, so multiplicities are retained.

The proof applies the published
`adjacentBlockSwap_of_twoBlock_and_length.{uF,uV,uW}` from
`AdjacentMatchingAssembly`. Its two inputs are discharged as follows:

- `twoBlockAssociatedCuspidalInductionFactors.{uF,uV,uV}` from
  `TwoBlockAssociationProof` supplies the full associated two-block theorem
  in the common universe used by the canonical tensor factors. It is a proved
  theorem, with no additional vanishing, filtration or intertwiner premise.
- `fun _ _ F T n => cuspidalInductionLength.{uF,uV} F T n` from
  `NormalizedCuspidalInductionLengthProof` supplies the full length theorem
  pointwise for every prime, field, topological datum and natural rank,
  including rank zero. Its conclusion contains group-algebra finite length
  and an actual composition series bounded by the factorial of the block
  count. The assembly uses its finite-length conclusion.

The imported assembly merges the two neighbouring blocks. It applies the
two-block theorem at the merged slot and the one-block comparison at the
other slots, then combines the matches by external tensor products. Published
normalized admissibility supplies the admissibility of both inner families.
The length theorem gives finite length for both global inductions of the
cuspidal tensor products. Actual normalized induction-in-stages equivalences
transfer these lengths to the outer inductions, where normalized induction
factor matching applies. Transport back through both stages equivalences
retains the matching composition series. Finally, the published canonical
tensor reduction recovers arbitrary inducing representations and the
independent target carrier universe `uW`.

All representation transports, positive half-modulus twists and right
translation actions are the existing canonical constructions in the Library.
The proof assumes neither the parent association theorem nor the cuspidal
association equivalence. Finite length and admissibility used inside the
assembly are derived from published results rather than added to the target.
The target statement pair and its imported pairs are unchanged.

This is an internal deduction from the three imported proof modules; it
introduces no new construction or literature transcription. The adjacent
step is the specialization of Bernstein–Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), sections 2.16(2) and 2.17, printed page
450/PDF page 11, documented in `AdjacentSwapStatement.md`. Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The implemented proof route is the published conditional assembly with both
of its full theorem inputs now supplied by their published proofs.
