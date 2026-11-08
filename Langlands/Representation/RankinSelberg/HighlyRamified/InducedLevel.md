# Principal level vectors of normalized inductions and of characters

Module `Langlands.Representation.RankinSelberg.HighlyRamified.InducedLevel`.

This module supports the proof of
`Langlands.RankinSelberg.HighlyRamifiedGammaStabilityStatement`. The comparison
argument of `HighlyRamified.MonomialGamma` needs a principal series whose principal
level is bounded by the level of the given representation. This module shows that
normalized induction, unramified twists and rank-one characters keep principal
level vectors (`HasPrincipalLevelVector`). It also proves the facts about central
characters that the comparison uses.

## Provenance

These are standard facts about smooth representations of `GL_n` over a p-adic
field. Jacquet and Shalika 1985, §4.2 (printed pages 326–327), use the principal
series without discussing its level. The formal derivations here are internal to
this project.

## Lemmas on inductions

All statements use the canonical topological data `F.canonicalTopologicalData`
of the p-adic field `F`. `K_r(a)` denotes
`Conductor.principalLevelSubgroup F.Carrier r a`, the group
`1 + ϖ^a M_(r+1)(O)` (the integral group when `a = 0`).

- `leviProjection_mem_principalLevelSubgroup F g hg i`: let `g` lie in the
  standard parabolic of block shape `succBlockShape m h` and in `K_t(a)`. Then its
  `i`-th Levi block lies in `K_(m i)(a)`. Membership is the entrywise condition
  `UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff` on the matrix and
  its inverse. The block entries are entries of `g`, and the entries of the
  inverse block are entries of `g⁻¹`.
- `parabolicHalfModulus_eq_one_of_mem F K hK q hq`: the half modulus
  `δ_P^(1/2)` of the parabolic is `1` on elements of a compact subgroup `K`. The
  modulus is a continuous homomorphism to positive reals, so it is trivial on the
  compact group `P ∩ K` (`LastRowReduction.eq_one_of_isCompact`).
- `tprod_ne_zero_of_ne_zero v hv`: a pure tensor of nonzero vectors is nonzero.
  Linear functionals with `φ_i(v_i) = 1` combine to a functional with value `1`
  on the tensor.
- `hasPrincipalLevelVector_normalizedProductInduced F h σ hσ`: if every block
  `σ_i` of `succBlockShape m h` has a nonzero vector fixed by `K_(m i)(a)`, then
  the normalized induction `F.canonicalNormalizedProductInduced` has a nonzero
  vector fixed by `K_t(a)`. Let `v_i` be the fixed vectors and `w` their tensor.
  For `q ∈ P ∩ K_t(a)` the half modulus is `1` and each Levi block of `q` fixes
  `v_i`. So `w` is fixed by `P ∩ K_t(a)`. The Library section
  `Induction.fixedDoubleCosetSection` at the representative `1` is then a
  `K_t(a)`-fixed vector with value `w ≠ 0` at `1`
  (`Induction.fixedDoubleCosetSection_eval_self`).

## Lemmas on characters

- `discreteValuation_integers F`: the integers of the discrete valuation are
  `F.canonicalTopologicalData.Integers`.
- `discreteValuation_eq_one_of_integral F hx0 hx hxinv`: a nonzero `x` with `x`
  and `x⁻¹` integral has valuation `1`.
- `discreteValuation_determinant_eq_one F hg`: the determinant of an element of
  `K_r(a)` has valuation `1`. It is the image of the determinant of an integral
  invertible matrix, which is a unit of `O`.
- `determinant_mem_principalUnits F hg`: in rank one, the determinant of an
  element of `K_0(a)` is a principal unit of level `a`, by the entry condition and
  `RankOneBox.levelSet_eq_additiveLattice`.
- `hasPrincipalLevelVector_rankOneExtensionCharacter F χ h`: if `a(χ) ≤ a`, then
  `rankOneExtensionCharacter F χ` (the character `χ ∘ det` on `ULift ℂ`) fixes
  `1` under `K_0(a)`, because `χ` is trivial on the principal units of level `a`.
- `multiplicativeConductor_unramifiedCharacter F z`: the unramified character
  `x ↦ z ^ ord(x)` has conductor exponent `0`.
- `exists_quasicharacter_hasGLCentralCharacter F ψ σ hσ`: a generic `σ` has a
  central character `ω`, and `ω` is continuous. Schur's lemma for admissible
  irreducible representations (`admissibleSchur_centralCharacter`) gives a
  locally constant character of the centre. Composing with the continuous scalar
  map gives `ω`.
- `multiplicativeConductor_le_of_hasGLCentralCharacter F σ ω hω h`: if `σ` has
  central character `ω` and a nonzero vector fixed by `K_n(m)`, then
  `a(ω) ≤ m`. For a principal unit `u` of level `m`, the scalar matrix `u` lies in
  `K_n(m)` (`scalar_mem_principalLevelSubgroup`), so `ω(u)` fixes a nonzero
  vector.
- `hasPrincipalLevelVector_twist_unramified F σ z h`: a twist by
  `μ_z ∘ det` with `μ_z` unramified keeps vectors fixed by `K_n(m)`. The
  determinant of an element of `K_n(m)` has valuation `1`, so `μ_z` is `1` on it.
