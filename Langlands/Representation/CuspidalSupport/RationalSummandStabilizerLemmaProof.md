# Renard VI.4.4, Lemma: proof

Author: Worker 33. Module
`Langlands.Representation.CuspidalSupport.RationalSummandStabilizerLemmaProof`, namespace
`Langlands.CuspidalSupport`.

`rationalSummandStabilizerLemma : RationalSummandStabilizerLemmaStatement.{uF, uV}` proves
the published statement of Renard's Lemma of VI.4.4 at arbitrary universes `uF` and `uV`,
with its premises unchanged. In the setting of the Theorem of VI.4.4 (`π` irreducible
cuspidal, `ρ` an irreducible smooth representation of `⁰G = rationalCommonNormKernel G`
occurring in `Res π`), the statement asserts that a good embedding `j : ρ → Res π` exists.
For every good `j` it asserts `T ⊂ H ⊂ N` with `[N : H] = [H : T] = m`, the bijectivity of
restriction (VI.4.4.3), and that the irreducible components of `Res_T π` containing `ρ` are
isomorphic to `ρ_T`. A good `j` is one whose image `W` satisfies Renard's choice `H = H̃`.
See `RationalSummandStabilizerLemmaStatement.md`.

## Proof

After introducing the binders and the topological-group instance on `G(F)`, the proof
applies the generic theorem `NormalHecke.lineStabilizer` (module
`NormalHeckeLineStabilizer`) with:

- `H = ⁰G`, open by `isOpen_rationalCommonNormKernel`;
- the degree `p g = Additive.ofMul (rationalValuationImageProjection G g)`, the valuation of
  rational characters written additively, whose kernel is `⁰G` (`isDegree_rationalValuation`);
- `rank ρ ≤ ℵ₀`, by `rank_le_aleph0_of_rationalCommonNormKernel`;
- finite dimension of `Hom(ind ρ, π)`, by `finiteDimensional_rationalSummandHom`. Its input
  is the finite-length clause of the published `rationalNormKernelFiniteRestriction`, the
  proof of Renard VI.3.2 (ii);
- `hcyc` and `hiso`, by `rationalSummand_cyclic_of_isIrreducible` and
  `rationalSummand_twistIso_of_isIrreducible` (module `NormalHeckeHomDetection`). The
  `Nontrivial` instance they need comes from `nontrivial_rationalSummandHom` and the given
  embedding;
- `hT`, by `mem_rationalTwistGroup_iff`. It says that `g` lies in the statement's `T` (the
  infimum of the kernels of the unramified `ω` with `π ⊗ ω ≅ π`) iff `ω g = 1` for every
  character `ω` with open kernel containing `⁰G` and `π ⊗ ω ≅ π`, which is the form of `hT`
  in `lineStabilizer`;
- `hex`, the given injective `j₀`.

All lemmas named in this list except `lineStabilizer` are published (modules
`RationalSummandEndCenterReduction`, `NormalHeckeHomDetection`,
`RationalNormKernelTopology`, `RationalNormKernelFiniteRestrictionProof`). The conclusion of
`lineStabilizer` is the statement's body with `H = ⁰G`, so it closes the goal.

The proof of `lineStabilizer` is described in `NormalHeckeLineStabilizer.md`, and its
algebraic core in `Langlands/Algebra/RankOneGradedLagrangian.md`. In outline:

- `End(ind ρ)` is graded by `G/⁰G` with pieces of rank at most one, and acts on
  `M = Hom(ind ρ, π)` (dimension `m`) through all of `End(M)`;
- `N`, `H` and `T` are the preimages of the support, the stabilizer of the line
  `ℂ e⁻¹(j)`, and the radical;
- a line containing its commutation-orthogonal (`perp`) gives a basis of `M` indexed by
  `support / stab`, which yields `[N : H] = m` and then `[H : T] = m` from `[N : T] = m²`;
- such a line exists by minimizing the index, and it corresponds to a good `j`;
- (VI.4.4.3) holds because elements of the radical act on `M` as the identity.

No premise is added. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Cuspidality of `π` and the torus, cocharacter and root-system premises are
carried by the statement but not used.

## Relation to the source

Source: David Renard, *Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, Lemma and its proof,
printed pp.157–158 / PDF pp.163–164, with the preliminary remarks on printed pp.155–157 /
PDF pp.161–163.

Renard's proof uses the decomposition (VI.4.4.2), `π ≃ ind_H^G ρ_H`, the replacement of `W`
to reach `H = H̃`, Proposition VI.3.2 (iii) adapted to `T` and `H`, the duality between tori
and lattices for `X(G)`, and the adjunction (VI.4.4.4) with `ind_T^H ρ_T ≃ ⊕_ξ ρ_H ⊗ ξ`.
The implemented proof uses none of these. It works with the Hecke algebra
`End(ind_{⁰G}^G ρ)` and its right action on `Hom(ind_{⁰G}^G ρ, π)`, as in the published proof
of the Theorem of VI.4.4 (`RationalSummandEndCenterProof`). Finiteness of `X(G)(π)` and of
`[G : T]` are not used.
