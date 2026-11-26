# Pointwise descent of relative Eisenstein wave packets

`Langlands.Global.relativeWavePacketDescent` proves
`Langlands.Global.RelativeWavePacketDescentStatement`. A relative wave packet
is left invariant under `A_G G(F)`, so evaluating it at the chosen
representative of the class of `g` in `[G]` gives its value at `g`.
[Statement](AdelicRelativeWavePacketDescentStatement.md)

For a rational point `x`, right multiplication by `x` permutes
`P(F) \ G(F)`. The summand at `xg` equals the summand at `g` indexed by
the translated coset, by `IsIwasawaCompact.eisensteinTerm_eq_of_representative`.
Reindexing `tsum` by this equivalence gives rational left invariance of the
defining sum.

For `z ∈ A_G`, `ParabolicRootPresentation.exists_intermediateSplitComponentFactor`
factors the split component of `G` through that of the Levi `M`.
Functoriality of the positive real subgroup gives a lift `q ∈ P(𝔸)` of `z`
through `A_M`. The map giving the lift is central in `P` because its
composite into `G` is central and `P → G` is a monomorphism.
`Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral` makes the
inducing half modulus at `q` equal to one, so the inducing form is invariant
under `z`. Centrality in `G` lets `z` pass the rational coset representative,
and the Iwasawa height under left multiplication by `q` multiplies each
twisted summand by `q^λ = exp(⟨λ, H_P(q)⟩)`.

For each inducing form, `eisensteinRegularParameter` and
`isOpen_setOf_isRegularParameter` give a nonempty open region in complex
linear coordinates where its supplied continuation agrees with the sum.
The function `λ ↦ q^λ` is entire since it is the exponential of a
complex-linear form. The proof uses
`IsMeromorphicInCoordinatesOn.eqOn_of_eqOn_open` to extend rational
invariance and central equivariance to the packet's supplied holomorphy
domain. At `λ = iμ` with `μ ∈ relativeParameterSpace p`, the defining
annihilator gives `⟨μ, H_P(q)⟩ = 0`. The imaginary pairing then gives
`q^λ = 1`. Both translations therefore preserve the integrand pointwise.
`LeftCosetSpace.invariant_sup` combines the two invariances, and
`LeftCosetSpace.out_mk_of_invariant` gives the representative identity.

## Sources

- Getz–Hahn, *An introduction to automorphic representations* (2024),
  §2.6, (2.20)–(2.22), pp. 68–69 (PDF pp. 85–86), defines `A_G` and `[G]`.
  Section 10.5, (10.21)–(10.24), pp. 281–282 (PDF pp. 293–294), uses the
  packet integral on the imaginary relative parameter space in `L²([G])`.
  The pointwise descent is the compatibility of that integral with this
  quotient for one parabolic. Source ID
  `getz-hahn-2024-automorphic-representations`, PDF SHA-256
  `a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
- Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
  (2024), §2.2, (2.1), p. 191 (PDF p. 5), gives the defining sum over
  `P(F) \ G(F)` and its regular region. Source ID
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein-published`,
  PDF SHA-256
  `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
- Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series* (2011), §2, p. 311 (volume PDF p. 320), defines the
  inducing form's `A_M` transformation law with factor `δ_P^{1/2}` and
  the twist by `exp(⟨λ, H_P⟩)`. Source ID
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
  SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`.
