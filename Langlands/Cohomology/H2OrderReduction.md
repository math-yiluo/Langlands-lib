# Order bounds for second cohomology from prime-index layers

Author: Worker 229. The module imports the published degree-two
inflation–restriction exactness `Langlands.Cohomology.h2InflationRestrictionExactness`
(module `Langlands.Cohomology.H2InflationProof`) and the published Sylow
module `Langlands.Cohomology.SylowDetectionProof`, without modification. From
the latter it uses the index law
`Langlands.Cohomology.index_nsmul_eq_zero_of_restriction_eq_zero`. Everything else here is new. The module is a generic,
group-theoretic helper: it mentions no number fields and no idele classes.

## What is proved

Fix a commutative ring `k`, a group `G` and a representation `A : Rep k G`, all
in one universe `u`. The module defines two hypotheses on `A`:

- `H1VanishesOnSubgroups A`: for every subgroup `H ≤ G`, the degree-one
  cohomology of `A` restricted to `H` is a subsingleton.
- `H2PrimeLayerBound A`: for every subgroup `H ≤ G` and every normal subgroup
  `N ⊴ H` of prime index, Mathlib's quotient representation
  `(Rep.res H.subtype A).quotientToInvariants N` of `H ⧸ N` on the
  `N`-invariants has finite degree-two cohomology, of order dividing the
  index `[H : N]`.

The main theorem `finite_card_dvd_of_primeLayers` states: if `G` is finite and
both hypotheses hold, then `groupCohomology A 2` is finite and its
`Nat.card` divides `Nat.card G`. The cohomology objects, restriction maps and
inflation maps are Mathlib's.

## Helpers

- `resSubgroupMapIso` identifies the cohomology of a subgroup `K` of a
  subgroup `H` (restricted in two steps) with the cohomology of the image of
  `K` in `G`. It is `groupCohomology.mapIso` for the isomorphism
  `K ≃* K.map H.subtype` and the identity on coefficients.
- `finite_card_dvd_of_exact` states that for `R`-linear maps
  `f : X₁ → X₂` and `g : X₂ → X₃` with `f` injective, `range f = ker g` and
  finite `X₁`, `X₃`, the middle term is finite and
  `#X₂ ∣ #X₁ · #X₃`. The proof uses `#X₂ = #(range g) · #(ker g)`, the
  isomorphism `ker g = range f ≅ X₁`, and Lagrange for `range g ≤ X₃`.

## The `p`-group case

`finite_card_dvd_of_isPGroup` proves, for a prime `p` and every `p`-subgroup
`H ≤ G`, that the degree-two cohomology of `A` restricted to `H` is finite of
order dividing `#H`. The proof is by strong induction on `#H`, for all
`p`-subgroups simultaneously.

If `#H = 1`, the group is trivial, so its positive-degree cohomology is zero
(`isZero_groupCohomology_succ_of_subsingleton`). Otherwise `p ∣ #H`. Since
`p`-groups are nilpotent, `Group.IsNilpotent.exists_normal_index_eq_of_dvd_card`
gives a normal subgroup `N ⊴ H` of index `p`. Degree-one vanishing on the image
of `N` in `G`, moved to `N` by `resSubgroupMapIso`, is the only hypothesis of
the published degree-two inflation–restriction exactness. That theorem gives
the exact sequence

`0 → H²(H/N, A^N) → H²(H, A) → H²(N, A)`

as Mathlib's `groupCohomology.HInfRes`. The left term is finite of order
dividing `p` by the prime-layer hypothesis. The right term is finite of order
dividing `#N` by induction, because the image of `N` in `G` is a `p`-subgroup
with `#N < #H`. `finite_card_dvd_of_exact` then gives finiteness and
`#H²(H, A) ∣ p · #N = #H`.

## The general case

For each prime factor `p` of `#G`, `finite_card_dvd_of_primeLayers` chooses one
Sylow `p`-subgroup `P_p`. By the `p`-group case, `H²(P_p, A)` is finite of order
dividing `p^{v_p(#G)}`, which is `#P_p` (`Sylow.card_eq_multiplicity`).

The published index law `index_nsmul_eq_zero_of_restriction_eq_zero` (from
`SylowDetectionProof`) states that, for finite `G` and positive degree, a class
whose restriction to a subgroup `H` vanishes is killed by `[G : H]`.

Let `φ` be the additive map from `H²(G, A)` to the finite product of the
`H²(P_p, A)`, given by restriction in each coordinate. It is injective. Every
class `x` is killed by `#G`: restriction to the trivial subgroup is zero, and
that subgroup has index `#G`. So if a prime `q` divided the additive order of
a nonzero `x` in the kernel, then `q` would divide `#G`. The restriction of `x`
to `P_q` is zero, so `[G : P_q] • x = 0` and `q` would divide `[G : P_q]`, which
`Sylow.not_dvd_index` forbids. Hence the order of `x` is one.

Injectivity makes `H²(G, A)` finite and identifies it with the range of `φ`.
Lagrange in the product then gives `#H²(G, A) ∣ ∏_p #H²(P_p, A)`, which divides
`∏_p p^{v_p(#G)} = #G` (`Nat.prod_primeFactors_coe_pow_factorization`).

## Source correspondence

Source: Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea Publishing,
2009, registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. Chapter XIV
§2, Lemma 1, printed pp.147–148 (PDF pp.156–157), reduces an order divisibility
`order of Hʳ(L/F) ∣ [L : F]^ν` to cyclic layers of prime degree, assuming exact
inflation–restriction sequences. This module is the case `r = 2`, `ν = 1`, used
in XIV §3, printed p.152 (PDF p.161). The source states the lemma for
formations. Here the formation data is a single finite group with one
representation and all its subgroups. The exactness hypothesis is replaced by
degree-one vanishing on every subgroup, which gives exactness through the
published theorem, as the end of the source's §2 explains.

The implemented route differs from the source in two ways:

- In the prime-power case, the source splits off an arbitrary proper normal
  subgroup and applies induction to both layers. The Lean proof always splits
  off a normal subgroup of index `p`, so the quotient layer is covered directly
  by the prime-layer hypothesis and induction is needed only for the subgroup.
- In the general case, the source uses the fact that restriction to a Sylow
  `p`-subgroup is injective on the `p`-primary part. The Lean proof derives the
  needed injectivity from the published index law, with one Sylow subgroup per
  prime, by the same order argument as the published proof of
  `Langlands.Cohomology.SylowDetection`. It does not apply that statement
  itself. The statement's hypothesis is vanishing on all Sylow subgroups, and
  the order of a product over all of them does not divide `#G` in general.
