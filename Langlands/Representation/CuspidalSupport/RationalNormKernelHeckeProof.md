# Proof of Renard VI.4.2: End(ind ρ) is the Hecke space H(G,ρ)

Author: Worker 1789.

`Langlands.CuspidalSupport.rationalNormKernelHecke_equiv` proves the published
`Langlands.CuspidalSupport.RationalNormKernelHeckeStatement.{uF, uV}` with both
universes arbitrary. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, VI.4.2, Proposition and proof, printed p.152 / PDF p.158 (registered
source `renard-2026-representations-groupes-reductifs-padiques`).

## Proof

After the field, the group and the instances of the statement are introduced,
the proof applies the generic development of the supporting module
`Langlands.Representation.CuspidalSupport.NormalSubgroupHecke` with
H = `rationalCommonNormKernel G`. The published `isOpen_rationalCommonNormKernel`
gives openness, and the published instance `rationalCommonNormKernel_normal` gives
normality. Irreducibility of ρ is the hypothesis `ρ.IsIrreducible`.

The equivalence is `NormalHecke.heckeEquiv`, α ↦ (g ↦ (w ↦ α(f_w)(g))), with f_w
the published `unitFunction`. Its codomain `heckeSubmodule H ρ` is definitionally
the published `rationalNormKernelHecke G ρ`, and `heckeConvolution H ρ` is
definitionally `rationalNormKernelConvolution G ρ`. The three clauses are:

1. the value formula e(α)(g)(w) = α(f_w)(g), which holds by definition
   (`heckeEquiv_apply`);
2. the inverse formula
   e⁻¹(φ)(v)(x) = ∑ᶠ_{q ∈ H⁰\H} φ(q.out)(v(q.out⁻¹ x)) (`eval_endOfHecke`);
3. e(α * β) = `rationalNormKernelConvolution G ρ (e α) (e β)`
   (`heckeEquiv_mul`).

The supporting module's Markdown describes these proofs. In outline:
φ_α is bi-invariant by the equivariance of α and of the unit map. Its support
meets finitely many cosets: irreducibility gives a nonzero w₀, and the vectors w
for which α(f_w) is supported in the cosets meeting the support of α(f_{w₀}) form
an invariant subspace containing w₀. The inverse is the published coset sum of
the H⁰-map w ↦ (x ↦ φ(x) w). The two maps are inverse to each other by the
published identities `cosetSum_comp_unitMap` and `cosetSum_unitMap`; the second
is Renard's decomposition (VI.4.2.2). The inverse formula and multiplicativity
come from reindexing the coset sums along q ↦ x q⁻¹ and from passing between H⁰\H
and H ⧸ H⁰, which are the same cosets because H⁰ is normal. This is Renard's
comparison of (VI.4.2.3) with (VI.4.2.4).

## Relation to the source

Renard proves the Proposition for an irreducible summand ρ of Res π, with π
supercuspidal. His computation uses only that ⁰G is open and normal and that
every f in the induced representation decomposes by (VI.4.2.2). The Lean proof
follows the same computation for every irreducible smooth ρ, as the statement
requires. It adds no hypothesis: no admissibility, finite dimensionality or
countability is used.
