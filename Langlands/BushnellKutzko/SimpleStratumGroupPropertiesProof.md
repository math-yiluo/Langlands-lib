# Subgroup properties of a simple stratum

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups*, Annals of Mathematics Studies 129 (1993), (3.1.14)–(3.1.15), printed
p. 95 (PDF p. 107). The retained source `bushnell-kutzko-1993-admissible-dual-gln`
has SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
The lattice input is (3.1.9)–(3.1.13), printed pp. 91–94.

`Langlands.BushnellKutzko.simpleStratumGroupProperties` proves
`SimpleStratumGroupPropertiesStatement` in independent field and vector-space
universes. The proof takes the given defining sequence and transfers its
additive lattice properties from `simpleStratumLatticeProperties` to the groups
of units.

1. For a subalgebra `R` and an element `g` of `U⁰(𝔄)` lying in `R`, the element
   `g⁻¹` lies in the finite ambient order and satisfies a monic polynomial over
   `𝔬_F`. If its degree is `d`, multiply the relation on the right by
   `g^d g⁻¹`. The leading term becomes `g⁻¹` and every other term is a scalar
   times a nonnegative power of `g`. This proves inverse closure, including at
   level zero. Together with multiplication and the unit it identifies the
   generated subgroups with the literal intersections in (3.1.14).
2. For either order, the defining-sequence recursion writes the additive
   lattice as `𝔅_β + I` with `I ⊆ 𝔓^a` for the corresponding cutoff `a`.
   The terminal condition identifies the finite depth in the empty-tail case.
   If `m < a`, decompose `g = b + x` in this sum. The endomorphism
   `e = 1 − g⁻¹x` is in `U^a(𝔄)` by the positive-depth filtration lemma.
   Now `ge = b` lies in the relative unit group at level `m`, and `e⁻¹`
   lies in the same subalgebra at level `a`. Thus `g = (ge)e⁻¹`. At `m = a`
   use the identity as the relative factor. The reverse inclusion uses
   `𝔅_β ⊆ R` and the decreasing ambient unit filtration. Applying this to
   the two cutoffs gives both pointwise products of (3.1.15)(i).
3. For units in the ambient filtration, membership in the literal intersection
   is equivalent to membership of `g − 1` in the corresponding lattice layer.
   The lattice-chain stabilizer preserves the ambient unit filtration. The
   relative normalizer preserves both layers by (3.1.11), so it also normalizes
   each group. The layer inclusion gives `Hᵐ ≤ Jᵐ`, and the decreasing
   filtration gives `Hᵐ⁺¹ ≤ J⁰`. Conjugation of the positive `H` layers by
   `J⁰` follows from their two-sided ideal property in `𝔍`.
4. For `g ∈ Jᵏ` and `t ∈ Jˡ`, with `k,l ≥ 1`, put `x = g − 1` and
   `y = t − 1`. The group commutator minus one is
   `(xy − yx)g⁻¹t⁻¹`. Both products belong to `ℌᵏ⁺ˡ` by (3.1.13)(ii).
   Right multiplication by `g⁻¹` and `t⁻¹` preserves that layer by its ideal
   property in `𝔍`. The bound for the subgroup follows by applying the
   commutator subgroup's generating property.

`simpleHGroup_mem_iff_of_pos` and `simpleJGroup_mem_iff_of_pos` apply the
intersection identities of the group properties to identify positive-depth
membership directly with membership of the difference from one in the
respective additive layer. At positive depth that condition forces membership
in the ambient unit filtration by `LatticeChain.exists_mem_unitFiltration`.
