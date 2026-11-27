# Ramification index and residue degree in a tower

For a nonarchimedean local field `F`, a finite extension `E/F` carrying
its spectral local-field structure (`LocalField.FiniteExtension`) and a
finite extension `K/E`, this module proves

- `isIntegral_spectralInteger_iff`: an element of `K` is integral over
  `𝒪[E]` exactly when it is integral over `𝒪[F]`;
- `subfieldIntegersTowerEquiv`: the two integral closures in `K` are the
  same subring;
- `subfieldRamificationIndex_tower`:
  `e(K|F) = e(E|F) e(K|E)` for the invariants `subfieldRamificationIndex`;
- `subfieldResidueDegree_tower`: `f(K|F) = f(E|F) f(K|E)` for
  `subfieldResidueDegree`.

## Proofs

Integrality transfers through the ring isomorphism
`subfieldIntegerEquiv F E` between the integral closure of `𝒪[F]` in `E`
and `𝒪[E]`, and through `isIntegral_trans` and `IsIntegral.tower_top`.

For the ramification indices, `baseUniformizer_factorization` writes a
uniformizer `π` of `F` as `u₁ ϖ_E^{e(E|F)}` in the integers of `E`, a
uniformizer of `𝒪[E]` as `u₂ ϖ_K^{e(K|E)}` in the integers of `K` over
`𝒪[E]`, and `π` as `u₃ ϖ_K^{e(K|F)}` in the integers of `K` over `𝒪[F]`.
The images of `u₁` and `u₂` are units of the integers of `K`
(`subfieldIntegersUnitMap`), and uniqueness of the exponent in a discrete
valuation ring (`IsDiscreteValuationRing.unit_mul_pow_congr_pow`) gives
`e(K|F) = e(E|F) e(K|E)`.

The residue degrees follow from `e f = [ : ]`
(`subfieldRamificationIndex_mul_residueDegree`) in the three extensions
and the tower law `Module.finrank_mul_finrank`.

These are the multiplicativity of ramification indices and residue
degrees used in Bushnell–Kutzko 1994,
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, (1.12), printed
p. 115.
