# Induced twisted traces of equivalent inducing representations

Let `E` be a nonarchimedean local field, `σ` an automorphism of `E` over
`F`, and `B` a block shape of `n`. This module moves induced twisted traces
along equivalences of inducing representations and between unnormalized
and normalized induction.

- `leviIntertwinerTransport σ B A e` transports a Levi σ-intertwiner `A`
  of `Ξ` along an equivalence `e : Ξ ≃ Ψ`. It is `e ∘ A ∘ e⁻¹`, viewed as a
  σ-intertwiner of `Ψ`.
- `blockFactors_sigmaStable`: if the block tensor of irreducible block
  representations `A i` is σ-stable on the Levi, then each block is
  σ-stable: `A i` is equivalent to the twisted block `(A i) ∘ σ`. By
  `blockTensor_comp_leviAut`, the σ-twist of the block tensor is the
  external tensor product of the twisted blocks. The σ-stability
  equivalence therefore makes the untwisted external product a
  subquotient (in the sense of `WeylBranchPieces.IsSubquotient`: a
  quotient of a subrepresentation) of the twisted external product.
  `FiniteTensor.isSubquotient_factor_of_external`, whose irreducibility
  hypothesis is on the untwisted blocks, then makes each untwisted block
  `A i` a subquotient of the twisted block `(A i) ∘ σ`. Both are
  irreducible, so they are equivalent
  (`CuspidalInductionJacquetConstituent.nonempty_equiv_of_isSubquotient`).
  The same argument appears privately in
  `Langlands.BaseChange.SigmaOrbitDiscreteness`.
- `isAdmissible_smoothInduced_levi`: unnormalized parabolic induction of an
  admissible Levi representation is admissible, since the parabolic
  quotient is compact.
- `twistedDistribution_inducedSigma_of_equiv`: equivalent inducing
  representations, with the transported intertwiner, have equal induced
  twisted traces. Induction carries the equivalence to an equivalence of
  induced representations (`Induction.smoothInducedEquiv`). It intertwines
  the two induced operators, and `twistedDistribution_eq_of_equivalent`
  applies.
- `inverseHalfModulus_leviAut`: the inverse half modulus is σ-invariant.
- `twistedDistribution_inducedSigma_eq_normalized`: the unnormalized
  induced twisted trace of `Ψ` equals the normalized induced twisted
  trace of `twist (leviHalfModulus B)⁻¹ Ψ`, with the twisted intertwiner.
  Twisting by the half modulus and its inverse returns `Ψ`
  (`twist_twist_inv`). The two induced operators have the same underlying
  map (`twistedDistribution_inducedSigma_congr`).

A twisted character depends only on the isomorphism class of the pair
formed by a representation and its intertwining operator. These are
bookkeeping identities expressing this for induced pairs.
