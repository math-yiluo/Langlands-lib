# Simple right modules separate the Hecke algebra of an open normal subgroup

Author: Worker 1789.

This is a supporting module for the proof of Renard's VI.4.3 Lemma
(`RationalNormKernelEndSeparationProof`). It extends the generic development of
`Langlands.Representation.CuspidalSupport.NormalSubgroupHecke` and
`Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeDomain`, in namespace
`Langlands.CuspidalSupport.NormalHecke`. Here G is a topological group, H a normal
subgroup and ρ a smooth complex representation of H. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.3, Lemma and its
proof, printed pp.154–155 / PDF pp.160–161, and the separation lemma B.III. The
declarations here are internal helpers. Their route is not Renard's; the section
"Relation to the source" compares the two.

## Results

- `countable_quotient_of_isOpen`: if G is a separable space and H is an open
  subgroup, then G ⧸ H is countable. Fix a countable dense set D. Each coset
  q.out H is open and nonempty, so it contains some d ∈ D, and then d H = q. Hence
  d ↦ d H maps D onto G ⧸ H.
- `heckeSample H ρ w₀`: for a fixed vector w₀, the linear map from the Hecke space
  `heckeSubmodule H ρ` to `G ⧸ H →₀ ρ` sending φ to q ↦ φ(q.out) w₀. Only finitely
  many of these values are nonzero, because the Hecke space consists of functions
  supported on finitely many cosets.
- `heckeSample_injective`: if ρ is irreducible and w₀ ≠ 0, `heckeSample H ρ w₀` is
  injective. Suppose φ(q.out) w₀ = 0 for every q, and φ(g) ≠ 0 for some g. Then
  φ(q.out) ≠ 0 for q = g H (`hecke_ne_zero_of_mk_eq`). This value is injective
  (`hecke_injective`) and sends w₀ to 0, which contradicts w₀ ≠ 0.
- `rank_heckeSubmodule_le`: if ρ is irreducible, G ⧸ H is countable and
  `Module.rank ℂ ρ ≤ ℵ₀`, then the Hecke space has rank at most ℵ₀. A nonzero w₀
  exists by irreducibility. The injective map `heckeSample H ρ w₀` bounds the rank
  by that of `G ⧸ H →₀ ρ`. By Mathlib's `rank_finsupp` that rank is
  #(G ⧸ H) · rank ρ ≤ ℵ₀ · ℵ₀ = ℵ₀.
- `rank_end_le`: if moreover H is open, then
  `Module.rank ℂ (End (inducedRep H ρ)) ≤ ℵ₀`. The linear equivalence `heckeEquiv`
  of `NormalSubgroupHecke` preserves rank.
- `separation`: assume H is open, G ⧸ H is countable with `UniqueProds (G ⧸ H)`, ρ
  is irreducible and `Module.rank ℂ ρ ≤ ℵ₀`. Let α ∈ R = `End (inducedRep H ρ)` act
  as zero on every simple module M over Rᵐᵒᵖ with carrier in `Type (max uG uV)`,
  that is, on every simple right R-module. Then α = 0. Proof: R is a domain
  (`isDomain` of `NormalSubgroupHeckeDomain`). So if α ≠ 0, then α is not
  nilpotent, and neither is `MulOpposite.op α` in Rᵐᵒᵖ. The algebra Rᵐᵒᵖ has
  rank at most ℵ₀ (`rank_end_le` transported along `MulOpposite.opLinearEquiv`).
  The published Renard B.III separation lemma `Langlands.Renard.unitalSeparation`,
  applied to Rᵐᵒᵖ, gives a left ideal I of Rᵐᵒᵖ such that Rᵐᵒᵖ ⧸ I is simple and
  `op α • I.mkQ 1 ≠ 0`. This contradicts the hypothesis on α for M = Rᵐᵒᵖ ⧸ I,
  whose carrier lies in the universe of R.

## Relation to the source

Renard proves the Lemma as follows. B.III shows that an element φ of the kernel
is nilpotent. Then u = 1 + φ and u' = 1 − φ² = 2u − u² are invertible, and the
description (VI.4.3.3) of the units of the twisted Laurent polynomial algebra A
forces u, hence φ, to be a scalar, so φ = 0. He then derives Corollary (i), that
A is a domain, from the Lemma. The Lean development reverses this order. The
domain property is proved first and independently, in `NormalSubgroupHeckeDomain`,
from unique products in G ⧸ H, and it replaces the description of the units: a
nilpotent element of a domain is zero. The B.III step is Renard's. The published
B.III statement requires the algebra to have countable dimension, which Renard's
proof of the Lemma does not mention; here it comes from the countability of
G ⧸ H and of the dimension of ρ.
