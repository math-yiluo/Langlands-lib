# Essential vectors after a highly ramified twist

Module `Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. It defines the
essential-vector input `EssentialPairInput n` used by the adjacent-rank step of
Jacquet–Shalika §4.4, and derives it from two statements that are hypotheses here and
are not proved: the essential-vector level statement
`Conductor.EssentialVectorLevelStatement` (JPSS 1981, Theorem (5.1)(ii), with Jacquet's
essential vector) and `UniformRankOneTwistStatement` (JS85, Proposition (2.2),
level-uniform).

## Provenance

Jacquet and Shalika 1985, (4.4), first paragraph (printed page 327), twist both
candidates by a character `ξ` of large conductor. Then `L(s, π_i ⊗ ξ) = 1`, and
`ε(s, π_i ⊗ ξ, ψ)` has exponent `r a(ξ)`, so both twists have the conductor exponent
`f = r a(ξ)`. They use the essential vectors of JPSS 1981 at that conductor, and they note
that by construction the two essential vectors agree on `P_r Z_r K_r(f)`. Since
`L(s, π_i ⊗ ξ) = 1`, Jacquet's characterization of the essential vector makes its
restriction to the mirabolic subgroup the `ψ`-indicator of `N · GL_(r-1)(O)`. Jacquet and
Shalika do not state this.

The Lean proof takes a different route from JS85. It never identifies the restriction
of a given essential vector. It starts from the function and constructs the vector:

1. `zeroCellWhittaker hϖ hψ m` is the `ψ`-Whittaker function on `GL_(m+1)` with
   value `ψ(u)` at `u k` (`u` upper unipotent, `k ∈ GL_(m+1)(O)`) and value `0` off
   `N · GL_(m+1)(O)`. It is the published `Iwasawa.cellFunction` of the indicator of
   the zero exponent. It is right `GL_(m+1)(O)`-invariant, so it is a mirabolic test
   function (`isMirabolicTestFunction_zeroCellWhittaker`). On `diag(ϖ^λ, 1)` it is the
   indicator of `λ = 0` (`zeroCellWhittaker_rankInclusion_torus`).
2. The published Kirillov lifting `Whittaker.modelKirillovTransfer` (with
   `whittakerTypeKirillov`) gives a vector `w` of the Whittaker model of `π ⊗ ξ ∘ det`
   equal to this function on the mirabolic subgroup.
3. Take a right `GL_(n+1)(O)`-invariant `W'` with `W'(1) = 1`. The corank-one
   integrand of `w` against `W'` is then right `GL_(n+1)(O)`-invariant, and on
   `ϖ^λ` it is the indicator of `λ = 0`. The published torus sum
   `QuotientTorusEnvelope.integrable_integral_eq_tsum_torus` therefore makes it
   integrable with integral `1`, for every compatible quotient measure and every `s`
   (`integrable_integral_corankOneIntegrand_zeroCell`). Measurability holds because
   every preimage is open. Apply this to Jacquet's spherical functions
   `W(·; x; ψ̄)`. Then `w` satisfies Jacquet's identity with the polynomial `1`, and
   `essentialFactor 1 x = 1`.
4. So `w` is an essential vector (`Conductor.IsEssentialVector`) once
   `L(s, π ⊗ ξ) = 1` is known. `UniformRankOneTwistStatement` gives the pair
   L-polynomial `1` against the trivial character of `GL_1`.
   `isCharacterLPolynomial_of_isPadicSymmetricLPolynomial` turns it into the standard
   L-polynomial for the rank-one quotient measure. It uses the block `j = 0` and
   `characterZetaValues_succ_eq`. The empty rectangular variable carries the unit
   point mass for any σ-algebra (`unequalRankZetaValues_dirac_congr`), and the rank
   relabelling is the identity.
5. The level statement, applied with the epsilon exponent `(n + 3) a(ξ)` from
   `UniformRankOneTwistStatement`, makes `w` fixed by `K_1((n + 3) a(ξ))`
   (`exists_levelFixed_zeroCell_modelVector`).

The normalizations of Jacquet's theorem are built from the canonical data. An
additive character of conductor exponent `0` has conductor `O`
(`hasIntegerConductor_of_additiveConductor_eq_zero`). The chosen uniformizer is a
uniformizing element of normalized absolute value `q⁻¹`
(`exists_uniformizingElement_normalizedAbs`). The normalized absolute value is one on
valuation units (`normalizedAbsoluteValue_eq_one`). A self-dual Haar measure exists
(`nonempty_selfDualHaar`, from `padicSelfDualMeasureExists`). The quotient measure is
the published `unipotentQuotientHaar`.

A model vector fixed by `K_1(f)`, `f ≥ 1`, with `w(1) = 1` makes every central
character trivial on `1 + 𝔭^f`. The reason is that the scalar `u ∈ 1 + 𝔭^f` lies in
`K_1(f)` (`scalar_mem_levelSubgroup`), so `ω(u) = ω(u) w(1) = w(u) = w(1) = 1`
(`trivialOnPrincipalUnits_of_levelFixed`). Here `TrivialOnPrincipalUnits` is the
predicate of `HighlyRamified.DualTarget`.

## Main definitions and theorems

- `EssentialPairInput n` (rank `n + 3`). Let `ψ` have conductor exponent `0`. For
  every level `m` there are a quasicharacter `ξ` and a level `f > 0` with the
  following property. Let `π₁, π₂` be generic representations of `GL_(n+3)(F)` with
  nonzero vectors fixed by `1 + ϖ^m M(O)`. Then there are nonzero Whittaker
  functionals `ℓ_i` of `π_i ⊗ ξ ∘ det` and vectors `w_i` of their models with these
  properties:
  - the `w_i` are fixed by `K_1(f) = Conductor.levelSubgroup F (n + 2) f`;
  - `w₁` and `w₂` agree on the mirabolic subgroup (last row `(0, …, 0, 1)`);
  - `w_i(1) = 1`;
  - every central character of `π_i ⊗ ξ ∘ det` is trivial on `1 + 𝔭^f`.

  No central-character hypothesis on `π₁, π₂` is needed.
- `essentialPairInput h2 h3 n : EssentialPairInput.{uF, uV} n`. Its hypotheses are
  `h2 : Conductor.EssentialVectorLevelStatement.{uF, uV}` and
  `h3 : UniformRankOneTwistStatement.{uF, uV}`. The proof takes `ξ` with
  `a(ξ) ≥ max B 1` from `padicQuasicharacterUnboundedConductor`, where `B` is the
  rank-one bound at rank `n + 3` and level `m`, and sets `f = (n + 3) a(ξ)`. The
  vectors are the Kirillov lifts of the same zero-cell function, so they agree on the
  mirabolic subgroup.
