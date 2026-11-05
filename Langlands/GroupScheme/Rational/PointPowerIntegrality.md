# Spectral integrality from commuting factors of a positive power

This internal adapter joins the compact-powers matrix argument to an explicit
factorization of an actual rational point. It does not construct a factorization
or assert the general anisotropic reductive spectral-integrality theorem.

If the powers of commuting points `x` and `y` lie in compact sets `C` and `D`,
the multiplication image of `C × D` is compact and contains every power of
`x * y`. `rationalPointsMulContinuousMap` bundles multiplication in the canonical
identity-test topology using the published `rationalPoint_isTopologicalGroup`.
This step needs a
topological commutative coefficient ring and an affine group scheme locally of
finite type.

Over an actual nonarchimedean local field, suppose that `g ^ m = x * y` for a
positive natural number `m`, with the commuting compact-power data above.
`CompactMatrixIntegrality` proves that the actual representation matrix of
`g ^ m` is integral over the canonical valuation integer subring.
`rationalMatrix` respects powers, and `IsIntegral.of_pow` descends integrality
to the actual matrix of `g`. The characteristic-polynomial coefficient lemma
and integral closure of valuation integers then give the bound `coeff ≤ᵥ 1`
for every coefficient.

All results retain an arbitrary base universe, every finite matrix dimension
including zero, and both local-field characteristics. They require neither
faithfulness nor semisimplicity of the representation. The compact sets,
commutation and positive-power factorization remain explicit hypotheses of
this auxiliary unit; the general group-theoretic reduction must supply them.
