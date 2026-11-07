# Proof of Renard VI.4.3, Corollary (ii): End(ind_{⁰G}^G ρ) is commutative exactly when Res π is multiplicity-free

Author: Worker 1789.

`Langlands.CuspidalSupport.rationalSummandEnd_commutative` proves the published
`Langlands.CuspidalSupport.RationalSummandEndCommutativeStatement.{uF, uV}` with both
universes arbitrary. Source: David Renard, *Représentations des groupes réductifs
p-adiques*, VI.4.3, Corollary (ii) and its proof, printed p.155 / PDF p.161 (registered
source `renard-2026-representations-groupes-reductifs-padiques`).

## Characters of G(F) ⧸ ⁰G separate points

`rationalNormKernelQuotient_exists_character_ne_one G q hq` proves that for every
q ≠ 1 in `rationalPoints G ⧸ rationalCommonNormKernel G` there is a character
ω : G(F) ⧸ ⁰G →* ℂˣ with ω(q) ≠ 1. It holds for every group scheme G over a
nonarchimedean local field F. The published `rationalNormKernelQuotientEquiv G`, followed
by the subgroup inclusion, gives an injective homomorphism f from the quotient to
`Multiplicative (rationalCharacters G →+ ℤ)`, the valuation y ↦ (χ ↦ ord_F χ(y)). Since
q ≠ 1, the additive homomorphism f(q) is nonzero, so f(q)(χ) = n ≠ 0 for some rational
character χ. The map ω(y) = 2^{f(y)(χ)}, with 2 as a unit of ℂ, is a character. If
ω(q) = 2ⁿ were 1, taking norms would give 2ⁿ = 1 in ℝ, hence n = 0 (Mathlib's
`zpow_eq_one_iff_right₀`), a contradiction.

## Main proof

After the field, the group, the torus, the cocharacter data and the instances of the
statement are introduced, the proof establishes second countability as in the published
`rationalNormKernelEnd_separation`. F is second countable by the published
`HarmonicAnalysis.GeneralLocalField.secondCountableTopology`, and so is the affine point
space of G. The rational points G(F) embed in it by `rationalPointsAffineHomeomorph`, so
G(F) is second countable, and so is its subspace ⁰G = `rationalCommonNormKernel G`. Hence
G(F) ⧸ ⁰G is countable (`NormalHecke.countable_quotient_of_isOpen`, since ⁰G is open by
the published `isOpen_rationalCommonNormKernel`). The vector `hom j w` is nonzero for any
w ≠ 0 in ρ, by injectivity of j, so `SmoothRep.hom j ≠ 0`.

The categorical Hom spaces of the statement are identified with spaces of equivariant
linear maps by `NormalHecke.homLinearEquiv`, and `NormalHecke.rank_le_one_iff_of_equiv`
transfers the bound "dimension at most one". The endomorphism ring
`End ((compactInductionFunctor ⁰G).obj (SmoothRep.toRep.obj ρ))` of the statement is
`End (NormalHecke.inducedRep ⁰G ρ)` by definition. The two directions then apply the
generic results of the supporting module
`Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeCommutative` with H = ⁰G.

- Commutative ⇒ multiplicity-free: for every irreducible σ of ⁰G,
  `NormalHecke.rank_le_one_of_commute` gives dim Hom_{⁰G}(σ, Res π) ≤ 1. Its hypotheses are
  irreducibility of ρ and π, the nonzero map `SmoothRep.hom j`, countability of
  G(F) ⧸ ⁰G, and `Module.rank ℂ ρ ≤ ℵ₀`, the published
  `Whittaker.MirabolicRigidity.rank_le_aleph0` for the separable group ⁰G.
- Multiplicity-free ⇒ commutative: the hypothesis for σ = ρ gives
  dim Hom_{⁰G}(ρ, Res π) ≤ 1. `NormalHecke.commute_of_rank_le_one` then needs only the
  injective map `SmoothRep.hom j` and the separating characters of the lemma above.

The cuspidality of π, the torus, the cocharacter and the root-system premises of the
statement are not used.

The supporting module's Markdown describes the generic arguments. Commutativity makes the
simple right module Hom_G(I, π) one-dimensional, by Dixmier's form of Schur's lemma. A
Clifford-type step passes from ρ to arbitrary σ. Conversely, the twists π ⊗ ω by
characters of G(F) ⧸ ⁰G give right modules of dimension at most one, on which commutators
act by zero. Dedekind's independence of characters shows that an element acting by zero on
all of them is zero.

## Relation to the source

Renard derives (ii) from the equivalence of categories M(G)[π] ≃ mod-A of VI.4.1 and the
Lemma of VI.4.3. The Lean proof uses neither, and it does not use the supercuspidality of
π. The forward direction proves simplicity of the right module Hom_G(I, π) directly, from
semisimplicity of the restriction of I to ⁰G. In the converse, Renard's simple modules
Hom_{⁰G}(ρ, Res(π ⊗ ω)) for unramified ω appear as the right modules attached to the
twists of π. Independence of characters replaces the Lemma. Renard's multiplicity m of ρ
is replaced by the bound for all irreducible σ required by the statement. The forward
direction proves that bound by a Clifford-type argument, and the converse uses only
σ = ρ. The proof adds no hypothesis to the statement.
