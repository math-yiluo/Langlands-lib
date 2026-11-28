# The uniform cuspidal expansion for finite families from its analytic inputs

Module `Langlands.Global.AdelicEisensteinUniformCuspidalExpansionReduction`. It proves

- `eisensteinUniformCuspidalExpansion_of_inputs (hAut hDec hDecay) :
  EisensteinUniformCuspidalExpansionStatement.{u}` from `ConstantTermAutomorphyStatement`,
  `AutomorphicExponentDecompositionStatement` and `LeviCuspFormRapidDecayStatement`, all at
  universe `u`;
- `eisensteinUniformCuspidalExpansionReduction : EisensteinUniformCuspidalExpansionReductionStatement.{u}`
  (module `AdelicEisensteinUniformCuspidalExpansionReductionStatement`), the same implication;
- `eisensteinUniformCuspidalExpansion_of_exponentDecomposition (hDec) :
  EisensteinUniformCuspidalExpansionStatement.{u}` from `AutomorphicExponentDecompositionStatement`
  alone;
- `eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness (hHC) :
  EisensteinUniformCuspidalExpansionStatement.{u}` from
  `Langlands.Automorphic.GroupSchemeFunctions.ParabolicHarishChandraFinitenessStatement.{u}`
  (module `Langlands.Automorphic.GroupSchemeHarishChandraFinitenessStatement`), Harish-Chandra's
  finiteness theorem for parabolic subgroups.

## The proof

The proof composes three implications.

1. `convergentCuspidalTestExpansion_uniform_of_inputs` (module
   `CuspidalTestExpansion.Reduction`, whose Markdown explains the construction) proves from the
   three inputs, for one inducing function \(\varphi\), the comparison of norm-one Levi pairings
   with cusp forms that corresponds to Bernstein–Lapid (6.20). Tested against any cusp form on
   \(M_J\), the constant term along \(P_J\) of \(E(\varphi,\lambda)\) minus that of the selected
   term is a finite sum of tested competing terms with affine exponents in \(\lambda\). The
   degree bound of the competing terms is chosen before the parameter, and the tested constant
   terms on the left are integrable. The proof unfolds the constant term into Bruhat pieces,
   using the integration identity of the geometric lemma (the Library theorem
   `geometricLemmaUnfolding`). The pieces with proper target pair to zero with cusp forms, and the
   selected piece cancels the subtracted term. Each remaining full-target piece \(v\) is
   decomposed by the exponent components of the full constant term \(C_{I_v}\varphi\), not of its
   cuspidal projection. The competing term coming from a component with unnormalized exponent
   \(\nu\) along \(I_v\) has unnormalized label
   `weylParameter (fam.l I_v) c_v π_v (ν + λ|) + offset_v` along \(J\). This label is the Weyl
   transport of \(\nu\) plus the restricted parameter, shifted by the Haar offset `offset_v` of
   the intertwining measure. The competing exponents therefore come from the exponents of the full
   constant terms, a list that may be larger than the cuspidal exponent lists of (6.20). The tested
   scalar identity, which is all that the target asserts, does not need the smaller list. The
   conclusion of the theorem is `ConvergentCuspidalTestExpansionUniformStatement` (module
   `AdelicEisensteinUniformCuspidalExpansionIdentity`), binder for binder.
2. `eisensteinUniformCuspidalExpansionOne_of_uniform` (same module) specializes it to the identity
   Weyl element and rewrites the selected intertwining integral as the twist, giving
   `EisensteinUniformCuspidalExpansionOneStatement`.
3. `eisensteinUniformCuspidalExpansion_of_one` (module
   `AdelicEisensteinUniformCuspidalExpansionFamily`) passes to finite families by linearity.

For `eisensteinUniformCuspidalExpansion_of_exponentDecomposition` the first and third inputs are
supplied by the Library theorems `constantTermAutomorphy` (module
`AdelicConstantTermAutomorphyProof`) and `leviCuspFormRapidDecay` (module
`AdelicLeviCuspFormRapidDecayProof`), so the exponent decomposition (every automorphic function on
`U_Q(𝔸) M_Q(F) \ G(𝔸)` is a finite sum of automorphic functions with generalized unnormalized
exponents) is the only remaining input. The Library theorem
`automorphicExponentDecomposition_of_parabolicHarishChandraFiniteness` (module
`AdelicAutomorphicExponentDecompositionReduction`) derives that decomposition from
Harish-Chandra's finiteness theorem for parabolic subgroups, which gives
`eisensteinUniformCuspidalExpansion_of_parabolicHarishChandraFiniteness`.

No hypothesis is added and the universe `u` is kept throughout.
