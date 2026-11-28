# Standard twisted traces as specializations of regular unramified families

Let `E` be a `p`-adic field with topological data `T`, and let `σ` be an
`F`-algebra automorphism of `E` with the supplied `F`-module topology.

- `realPowerParameter T s` is the unramified parameter of the real
  determinant power `|det|^s`.
  `determinantPowerCharacter_eq_determinantUnramified` identifies
  `T.determinantPowerCharacter m s` with
  `determinantUnramified E m (realPowerParameter T s)`.
- `temperedDatum_blocks_isAdmissible` gives admissibility of the blocks of
  a tempered datum. `leviHalfModulus_leviAut_padic` gives σ-invariance of
  the half modulus `T.leviHalfModulus B`.
- `standardTrace_eq_standardFamilyTrace`: for an ordered tempered datum `t`
  and block intertwiners `A`, the twisted trace of the σ-stable standard
  module with the operator `temperedStandardSigmaIntertwiner` equals
  `unramifiedFamilyTrace` of the tempered blocks. That family has shape
  `t.shape`, the identity slot map, normalizing character
  `T.leviHalfModulus t.shape`, and parameters
  `realPowerParameter T (t.exponent i)`. The proof rewrites the twist of
  the family inducing representation by `twist_familyInducing`, so that it
  becomes the half modulus twist of the tensor of the twisted blocks. It
  then compares the two induced σ-intertwiners by
  `twistedDistribution_inducedSigma_congr`. They have the same underlying
  linear map.
- `normalizedProduct_unitaryTwist`: twist irreducible unitarizable blocks
  `δ i` by unitary unramified characters
  `determinantUnramified E (B.size i) (z (g i))` with `‖z k‖ = 1`. Their
  normalized product is irreducible and unitarizable. The proof applies
  `Classification.bernsteinUnitaryProductIrreducibility` to the twisted
  blocks, which remain irreducible and unitarizable.
- `isUnitarizable_of_isTempered`: an irreducible tempered representation of
  `GL_m(E)` with `m > 0` is unitarizable, by `glTemperedUnitarity`.

The irreducibility of unitary products is Bernstein (1984), Corollary 8.2
a), p. 89, and Tadić (1986), Theorem 2.5(i), p. 346. In Henniart–Lemaire
(2011), II.5.9, pp. 107–108, the standard σ-representation of a σ-stable
Langlands triplet `(α, Ξ, ψ)` is the parabolic induction of the tempered
Levi datum `Ξ` twisted by a real unramified character `ψ`. Here `ψ` is
positive with respect to the parabolic `P_α(E)`: its real exponents
satisfy `a_1 < ⋯ < a_m` (II.5.8, p. 106). They are not required to be
positive numbers. The Library's tempered data instead use strictly
decreasing real exponents. The first theorem identifies the twisted
trace of the standard module with the value of the corresponding
unramified family at a real parameter.
