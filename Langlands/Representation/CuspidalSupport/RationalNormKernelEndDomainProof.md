# Proof of Renard VI.4.3, Corollary (i): End(ind_{⁰G}^G ρ) is a domain

Author: Worker 1789.

`Langlands.CuspidalSupport.rationalNormKernelEnd_isDomain` proves the published
`Langlands.CuspidalSupport.RationalNormKernelEndDomainStatement.{uF, uV}` with both
universes arbitrary. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, VI.4.3, Lemma and Corollary, printed p.155 / PDF p.161 (registered
source `renard-2026-representations-groupes-reductifs-padiques`).

## Unique products in G(F) ⧸ ⁰G

`rationalNormKernelQuotient_uniqueProds G` proves
`UniqueProds (rationalPoints G ⧸ rationalCommonNormKernel G)` for every group
scheme G over a nonarchimedean local field F. The published
`rationalNormKernelQuotientEquiv G` identifies the quotient with the image of the
valuation g ↦ (χ ↦ ord_F χ(g)), a subgroup of
`Multiplicative (rationalCharacters G →+ ℤ)`. Composing with the subgroup
inclusion and with the coercion of additive homomorphisms to functions gives an
injective monoid homomorphism into `Multiplicative (rationalCharacters G → ℤ)`.
Mathlib provides unique sums for ℤ (a linearly ordered cancellative group), for
function types with values in a group with unique sums, and hence unique
products for the multiplicative version. Mathlib's
`UniqueProds.of_injective_mulHom` pulls the property back along the injective
homomorphism.

## Main proof

After the field, the group and the instances of the statement are introduced,
the proof applies `NormalHecke.isDomain` of the supporting module
`Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeDomain` with
H = `rationalCommonNormKernel G`. Openness is the published
`isOpen_rationalCommonNormKernel`, normality is the published instance
`rationalCommonNormKernel_normal`, irreducibility of ρ is the hypothesis
`ρ.IsIrreducible`, and unique products come from the lemma above. The
compactly induced representation `NormalHecke.inducedRep H ρ` is by definition
the published `compactInductionFunctor H` applied to `SmoothRep.toRep.obj ρ`,
the representation of the statement; its endomorphism ring
`End (NormalHecke.inducedRep H ρ)` is the ring of the statement.

The supporting module's Markdown describes the generic argument: through the
Hecke equivalence of VI.4.2, composition becomes convolution of Hecke functions;
for nonzero φ and ψ, a unique product of their coset supports in G(F) ⧸ ⁰G
isolates a single term of the convolution, a composite of an injective value of
φ with a nonzero value of ψ.

## Relation to the source

Renard derives (i) from the Lemma of VI.4.3 and the structure of H(G,ρ) as a
twisted Laurent polynomial algebra over ⁰G\N. The Lean proof uses the leading-term
idea on G(F) ⧸ ⁰G directly, without the grading by ⁰G\N, the bound on the
dimension of its pieces, or the Lemma. It adds no hypothesis on ρ beyond
irreducibility and smoothness: no admissibility, finite dimensionality, countability
or supercuspidal π is used. It also needs no reductivity for the unique-product
lemma, which holds for every group scheme over F.
