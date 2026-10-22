# The inverse-coset sum

Author: Worker 45.

Let `H` be a subgroup of a group `G` with finitely many left cosets, and let
`A` be a representation of `G` over a commutative ring `R`. For each left
coset `q ∈ G ⧸ H`, Mathlib's quotient supplies a fixed representative
`q.out`. `inverseCosetSum H A` is the `R`-linear endomorphism of `A` given by
the sum over all left cosets of the action of `q.out⁻¹`. The lemma
`inverseCosetSum_apply` gives its value on a vector `a` as
`∑ q, q.out⁻¹ • a`, and `inverseCosetSum_naturality` says that every
morphism of representations commutes with it.

The map depends on the chosen representatives; it is only used after
passing to quotients (`H`-coinvariants, or Tate classes) on which this
choice no longer matters. Neither `G` nor `H` needs to be finite.

This is the coefficient map underlying the relative norm
`N'_{G/H}(a) = Σ s⁻¹ a`, `A_G → A_H`, of Serre, *Local Fields* (1979),
Chapter VII, section 7, printed p. 119 (PDF p. 125), which defines
restriction on homology in degree zero. Source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
