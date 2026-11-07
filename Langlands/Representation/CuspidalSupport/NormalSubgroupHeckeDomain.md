# The Hecke algebra of an open normal subgroup is a domain

Author: Worker 1789.

This is a supporting module for the proof of Renard's VI.4.3 Corollary (i)
(`RationalNormKernelEndDomainProof`). It extends the generic development of
`Langlands.Representation.CuspidalSupport.NormalSubgroupHecke`, in namespace
`Langlands.CuspidalSupport.NormalHecke`. Here G is a topological group, H an open
normal subgroup and ρ an irreducible smooth complex representation of H. Source:
David Renard, *Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.3, printed
pp.154–155 / PDF pp.160–161. The declarations here are internal helpers. Their
route is not Renard's; the section "Relation to the source" compares the two.

## Results

- `hecke_ne_zero_of_mk_eq`: if φ is in `heckeSubmodule H ρ` and φ(g) ≠ 0, then
  φ(g') ≠ 0 for every g' with g' H = g H. Indeed g = g' k with k ∈ H, and
  φ(g' k) = φ(g') ρ(k) by right H-invariance (`hecke_mul_right`).
- `hecke_injective`: if φ(g) ≠ 0, then φ(g) is injective. For k ∈ H, the element
  g k g⁻¹ lies in H by normality, and bi-invariance gives
  φ(g) ρ(k) = φ(g k) = φ((g k g⁻¹) g) = ρ(g k g⁻¹) φ(g). So φ(g) intertwines ρ with
  its conjugate, its kernel is an invariant subspace, and irreducibility makes it
  zero (`injective_of_twisted` of `NormalSubgroupHecke`).
- `heckeConvolution_ne_zero`: assume `UniqueProds (G ⧸ H)`. If φ and ψ are
  nonzero elements of the Hecke space, their convolution
  `heckeConvolution H ρ φ ψ` is nonzero. Proof: the cosets meeting the supports
  of φ and ψ form finite nonempty sets S, T ⊆ G ⧸ H (finiteness is part of the
  definition of the Hecke space). By unique products there are a = gH ∈ S and
  b = yH ∈ T whose product a b is obtained from S × T only as a · b. In the
  convolution at x = g y,
  ∑ᶠ_{q ∈ G ⧸ H} φ(q.out) ψ(q.out⁻¹ g y), a term with q ≠ a vanishes: otherwise
  q ∈ S and (q.out⁻¹ g y) H ∈ T, and their product is a b, so q = a by
  uniqueness. Hence the value at g y is φ(a.out) ψ(a.out⁻¹ g y). Both factors are
  nonzero by `hecke_ne_zero_of_mk_eq`, because a.out H = g H and
  (a.out⁻¹ g y) H = y H. The first factor is injective by `hecke_injective`, so
  the composite is nonzero.
- `noZeroDivisors`: with H open and `UniqueProds (G ⧸ H)`,
  `End (inducedRep H ρ)` has no zero divisors. The linear equivalence
  `heckeEquiv` of `NormalSubgroupHecke` is injective and turns composition into
  convolution (`heckeEquiv_mul`), so the previous result applies.
- `nontrivial`: with H open, `End (inducedRep H ρ)` is nontrivial. For w₀ ≠ 0
  (`exists_ne_zero_of_isIrreducible`), the value of `heckeEquiv 1` at 1 sends w₀
  to f_{w₀}(1) = w₀ (the published `eval_unitFunction_one`), while that of
  `heckeEquiv 0` sends w₀ to 0.
- `isDomain`: with H open and `UniqueProds (G ⧸ H)`, `End (inducedRep H ρ)` is a
  domain, by Mathlib's `NoZeroDivisors.to_isDomain`.

## Relation to the source

Renard deduces the Corollary from the structure of A = H(G,ρ) as a twisted
Laurent polynomial algebra over the lattice ⁰G\N, N the stabilizer of ρ: A is
graded with pieces of dimension at most one, and nonzero homogeneous elements
multiply to nonzero elements (VI.4.3.1). The Lean proof does not use the grading
or the dimension bound. It keeps only two of Renard's ingredients: a nonzero
value φ(g) intertwines ρ with a conjugate and is therefore injective (Renard's
use of Schur's lemma for the pieces F_x(ρ)), and the leading-term argument, here
in the form of Mathlib's `UniqueProds` for the coset supports in G ⧸ H. For
H = ⁰G, the proof module `RationalNormKernelEndDomainProof` supplies unique
products for G ⧸ ⁰G: the quotient embeds in the group
`Multiplicative (X*(G) → ℤ)` of all integer-valued functions on the rational
characters, which has unique products because ℤ has unique sums and unique sums
pass to function types. No freeness of that full function group is used; it is
a different object from Renard's finite-rank lattice ⁰G\N.
