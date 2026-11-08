# Bilateral shell sums of the canonical Euler tests

Worker 1692 derives this internal support for the global Hecke theorem from the
published p-adic Fourier formulas, conductor laws and geometric series.
`shellMellinTerm` samples the actual canonical uniformizer and multiplies by the
integral power of the actual character value times the spectral variable. The
proved exponential formula identifies this with
`f(π^k) χ(π)^k exp(-k s log q)`.

The original canonical test has bilateral `HasSum` equal to the original local
`lFactor` when `ConvergesAt` holds for the original character and canonical
uniformizer. For an unramified character the nonnegative terms form a geometric
series and every negative term vanishes. For a ramified character only the
zeroth term survives. The separate translated-geometric-tail lemma works for
any integer starting index and retains every finite negative term. Inversion
preserves the exact constructed multiplicative conductor.

For the plus Fourier transform, with the inverse character in the Mellin term,
`hasSum_fourier_eulerTest` gives exactly
`epsilon T χ ψ μ.measure (1 - s) * lFactor T χ⁻¹ s`.
The convergence assumption is `ConvergesAt` for that inverse character.
In the unramified case the lattice indicator permits precisely `k ≥ -n`, where
`n` is the constructed additive conductor. The integer-ring mass multiplies the
translated geometric series; its initial factor equals the original unramified
epsilon expression at `1 - s`. In the ramified case only `k = -(n + a)`
survives, where `a` is the constructed multiplicative conductor. The actual
character values cancel, and combining the exponential factors with
`epsilonAt_eq_zero_mul` gives exactly the epsilon expression at `1 - s`.
The ramified coefficient formula itself is proved at every complex parameter.

All sums run over the integers with the unconditional `HasSum` meaning. The
geometric bound is the already proved equivalence with `ConvergesAt`. No
self-duality or Haar normalization is assumed; the original supplied Haar
measure occurs throughout. These local identities do not establish analytic
continuation or the global functional equation.
