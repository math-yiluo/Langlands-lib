# Irreducible subrepresentations of `𝔄 × E`

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Uniqueness`.

An internal module of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`. It proves
the socle half of the uniqueness of the highest left `A`-derivative. Take a supercuspidal
representation `A` of `GL_d` (`d > 0`), an irreducible `A`-pure representation `𝔄` of
`GL_a` (`a > 0`) and an irreducible left `A`-reduced representation `E` of `GL_m`
(`m > 0`). Then the normalized product `𝔄 × E` has an irreducible socle, so any two
irreducible subrepresentations of `𝔄 × E` are isomorphic. This is the standard
multiplicity-one argument (Zelevinsky 1980; Mínguez 2009 for the general form). Only the
mathematics stated in the Lean declarations below is claimed.

## Declarations

* `nonempty_iso_of_hasIrreducibleSocle`: if a smooth representation `P` of a topological
  group has an irreducible socle (`HasIrreducibleSocle`), any two irreducible smooth
  subrepresentations `π`, `π'` of `P` are isomorphic. Proof: each is isomorphic to the socle
  subrepresentation. `SmoothRep.isIrreducibleSocle_socleSubrepresentation_iff` turns the
  hypothesis into `IsIrreducibleSocle` for `P.socleSubrepresentation`. Its uniqueness clause
  `socle_eq` shows that an embedded `ρ` is also an irreducible socle of `P`, and
  `SmoothRep.nonempty_iso_socleSubrepresentation` gives the isomorphism.
* `hasIrreducibleSocle_productInduction` (generic form): fix a block shape `C` of `n` and a
  family `Y` of smooth representations of the blocks. Suppose the external tensor product
  `X = ⊠ Y` is irreducible. Suppose also that every Jordan–Hölder multiplicity of `X` in the
  Jacquet module along `C` of the normalized induction of `X` from `C` equals `1`. If the
  normalized product `×_C Y` has an irreducible smooth subrepresentation, then its socle is
  irreducible. Proof: the induction and its Jacquet module have finite length
  (`Parabolic.normalizedParabolicFiniteLength`). The chosen multiplicity
  (`compositionMultiplicity_witness`) is therefore `1`, and this is the multiplicity of `X`
  in `(upperFunctor T C).obj (×_C Y)` by definitional unfolding. The socle half of the
  Library's `multiplicityOneConstituentCriterion` applies to the functor `upperFunctor T C`
  with test object `X`. Its positivity hypothesis is
  `upperJacquetSubrepresentationDetection`: an irreducible subrepresentation `P` has nonzero
  inclusion, since `P` is nontrivial (`nontrivial_of_isIrreducible`). So `X` occurs in the
  Jacquet module of `P` with positive multiplicity.
* `hasIrreducibleSocle_twoBlock`: the generic form for `C = (a, m)` and `Y = (𝔄, E)`
  (`twoBlockFactors`). Irreducibility of `𝔄 ⊠ E` is `isIrreducible_twoBlock` (module
  `Core`). The multiplicity hypothesis is `multiplicity_eq_one_jacquetInduction` (module
  `Core`), which uses that `A` is supercuspidal, `𝔄` is `A`-pure and `E` is left
  `A`-reduced. As in the generic form, the existence of one irreducible subrepresentation is
  a hypothesis.
* `nonempty_iso_of_isSubrepresentation_binaryProduct`: under the hypotheses on `A`, `𝔄`, `E`
  above, any two irreducible smooth subrepresentations `π`, `π'` of the binary normalized
  product `(T.binaryNormalizedProductFunctor a m).obj (𝔄, E)` are isomorphic. Proof: transfer
  both embeddings along `SegmentSocleDerivativesProof.nonempty_ofPairProductIso` to the block
  product from `(a, m)` (`isSubrepresentation_of_iso`, module `PowerSupport`). Then apply
  `hasIrreducibleSocle_twoBlock`, with `π` as the required irreducible subrepresentation,
  and `nonempty_iso_of_hasIrreducibleSocle`.
