# Proof of Renard VI.4.3, Lemma: simple right modules separate End(ind_{⁰G}^G ρ)

Author: Worker 1789.

`Langlands.CuspidalSupport.rationalNormKernelEnd_separation` proves the published
`Langlands.CuspidalSupport.RationalNormKernelEndSeparationStatement.{uF, uV}` with
both universes arbitrary. Source: David Renard, *Représentations des groupes
réductifs p-adiques*, VI.4.3, Lemma and its proof, printed pp.154–155 / PDF
pp.160–161 (registered source
`renard-2026-representations-groupes-reductifs-padiques`).

## Main proof

After the field, the group and the instances of the statement are introduced,
the proof establishes second countability. F is second countable by the published
`HarmonicAnalysis.GeneralLocalField.secondCountableTopology`, and so is the affine
point space of G (`affinePointsSecondCountableTopology`). The rational points
G(F) embed in it by the published `rationalPointsAffineHomeomorph`, so G(F) is
second countable, and so is its subspace ⁰G = `rationalCommonNormKernel G`. This
follows the pattern of the published `exists_scalar_rationalPoint_center` in
`RationalPointCentralCharacter`. Second countable spaces are separable.

The proof then applies `NormalHecke.separation` of the supporting module
`Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeSeparation` with
H = ⁰G. Its hypotheses are supplied as follows:

- openness: the published `isOpen_rationalCommonNormKernel`;
- normality: the published instance `rationalCommonNormKernel_normal`;
- irreducibility of ρ: the hypothesis `ρ.IsIrreducible`;
- unique products in G(F) ⧸ ⁰G: `rationalNormKernelQuotient_uniqueProds` of
  `RationalNormKernelEndDomainProof`;
- countability of G(F) ⧸ ⁰G: `NormalHecke.countable_quotient_of_isOpen`, since
  ⁰G is open and G(F) is separable;
- `Module.rank ℂ ρ ≤ ℵ₀`: the published
  `Whittaker.MirabolicRigidity.rank_le_aleph0`, which bounds the dimension of an
  irreducible smooth representation of a separable group, here ⁰G.

The compactly induced representation `NormalHecke.inducedRep H ρ` is by
definition the published `compactInductionFunctor H` applied to
`SmoothRep.toRep.obj ρ`, which is the object I of the statement; its
endomorphism ring End I is the ring of the statement. The hypothesis on α in the statement, over all simple
modules over (End I)ᵐᵒᵖ with carrier in `Type (max uF uV)`, is the hypothesis of
`NormalHecke.separation` with uG = uF.

The supporting module's Markdown describes the generic argument. End I is a
domain, so a nonzero α is not nilpotent. End I has countable dimension, because
the Hecke equivalence of VI.4.2 embeds it in finitely supported functions from
the countable set G(F) ⧸ ⁰G to ρ. Renard's separation lemma B.III, published as
`Langlands.Renard.unitalSeparation` and applied to (End I)ᵐᵒᵖ, then gives a
simple right module on which α acts nontrivially.

## Relation to the source

Renard shows that a kernel element is nilpotent by B.III. He then concludes that
it is zero from the description of the units of the twisted Laurent polynomial
algebra (VI.4.3.3). The Lean proof keeps the B.III step. It replaces the unit
argument by the domain property, Corollary (i), which is proved independently of
the Lemma in `RationalNormKernelEndDomainProof`. The proof adds no hypothesis on
ρ beyond irreducibility and smoothness.
